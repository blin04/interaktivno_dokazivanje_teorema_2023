#print Or

example : p ∧ q ↔ q ∧ p :=
  have ltr : p ∧ q → q ∧ p :=
    λ hpq : p ∧ q =>
      have hp : p := And.left hpq
      have hq : q := And.right hpq
      And.intro hq hp
  have rtl : q ∧ p → p ∧ q :=
    λ hqp : q ∧ p => 
      have hp : p := And.right hqp
      have hq : q := And.left hqp
      And.intro hp hq
  Iff.intro ltr rtl

example : p ∨ q ↔ q ∨ p :=
  have ltr : p ∨ q → q ∨ p :=
    λ hpq : p ∨ q => by
      cases hpq with
      | inl hp => exact Or.inr hp 
      | inr hq => exact Or.inl hq
  have rtl : q ∨ p → p ∨ q :=
    λ hqp : q ∨ p => by
      cases hqp with
      | inr hp => exact Or.inl hp
      | inl hq => exact Or.inr hq
  Iff.intro ltr rtl
      

example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  have ltr : (p ∧ q) ∧ r → p ∧ (q ∧ r) := by
    intro hpqr
    have hpq := hpqr.left 
    have hp := hpq.left
    have hq := hpq.right
    have hr := hpqr.right
    apply And.intro hp (And.intro hq hr)
  have rtl : p ∧ (q ∧ r) → (p ∧ q) ∧ r := by
    intro hpqr
    have hqr := hpqr.right
    have hp := hpqr.left
    have hq := hqr.left
    have hr := hqr.right
    apply And.intro (And.intro hp hq) hr
  apply Iff.intro ltr rtl
  
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  apply Iff.intro
  . intro inl 
    cases inl with
    | inr hr => exact Or.inr $ Or.inr hr
    | inl hpq => 
      cases hpq with
      | inl hp => exact Or.inl hp
      | inr hq => exact Or.inr (Or.inl hq)
  . intro inr
    cases inr with
    | inl hp => exact Or.inl (Or.inl hp)
    | inr hqr => 
      cases hqr with
      | inr hr => exact (Or.inr hr)
      | inl hq => exact Or.inl (Or.inr hq)  
  

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := 
  sorry

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  sorry

example : (p → (q → r)) ↔ (p ∧ q → r) :=
  sorry

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  sorry

-- Demorganovi zakoni
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  have ltr : ¬(p ∨ q) → ¬p ∧ ¬q :=
    fun h : ¬(p ∨ q) =>
      have hnp : ¬p := (fun hp : p => h (Or.inl hp))
      have hnq : ¬q := (fun hq : q => h (Or.inr hq))
      And.intro hnp hnq
  have rtl : ¬p ∧ ¬q → ¬(p ∨ q) := 
    fun h : ¬p ∧ ¬q => 
      fun h₁ : p ∨ q => 
        Or.elim h₁
          (fun hp : p => h.left hp)
          (fun hq : q => h.right hq)
  Iff.intro ltr rtl 

#check Classical.em

example : ¬p ∨ ¬q ↔ ¬(p ∧ q) :=
  have ltr : ¬(p ∧ q) → ¬p ∨ ¬q :=
    fun h : ¬(p ∧ q) => 
      Or.elim (Classical.em p) 
      (fun hp : p => 
        have hnq : ¬q := fun hq : q => h (And.intro hp hq)  
        Or.inr hnq
      )
      (fun hnp : ¬p => Or.inl hnp)
  have rtl : ¬p ∨ ¬q → ¬(p ∧ q) :=
    fun h : ¬p ∨ ¬q => 
      fun h₁ : p ∧ q => 
        Or.elim h
          (fun hnp : ¬p => hnp h₁.left)
          (fun hnq : ¬q => hnq h₁.right)
  Iff.intro rtl ltr

-- Zakon neprotivrečnosti
example : ¬(p ∧ ¬p) :=
  sorry

example : p ∧ ¬q → ¬(p → q) :=
  sorry

example : ¬p → (p → q) :=
  sorry

example : (¬p ∨ q) → (p → q) :=
  sorry

example : p ∨ False ↔ p :=
  sorry

example : p ∧ False ↔ False :=
  sorry

example : (p → q) → (¬q → ¬p) :=
  sorry

open Classical

theorem dne {p : Prop} (h : ¬¬p) : p :=
  sorry

theorem imp_or {p q : Prop} (h : p → q) : ¬p ∨ q :=
  sorry

theorem or_imp {p q : Prop} (h : ¬p ∨ q) : p → q :=
  sorry

variable (p q r s : Prop)

example : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
  sorry

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  sorry

example : ¬(p → q) → p ∧ ¬q :=
  sorry

example : (p → q) → (¬p ∨ q) :=
  sorry

example : (¬q → ¬p) → (p → q) :=
  sorry

example : p ∨ ¬p :=
  sorry

example : (((p → q) → p) → p) :=
  sorry

------------------------------ Logika prvog reda -------------------------------

variable (p q : α → Prop)

example {α : Type} {φ : α → Prop} : (∀ x : α, φ x) ↔ (¬ ∃ x : α, ¬ φ x) :=
  sorry

example {α : Type} {φ : α → Prop} : (∃ x : α, φ x) ↔ ¬(∀ x : α, ¬ φ x) :=
  sorry

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  sorry

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  sorry

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  sorry

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  sorry

example {road : Type} {toRome : road → Prop} :
    ¬ ∀ r : road, toRome r → ∃ r : road, ¬ toRome r :=
  sorry
