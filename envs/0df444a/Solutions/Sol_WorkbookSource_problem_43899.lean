-- Prove2me | solution 1 for WorkbookSource.problem_43899
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:52:08.050447+00:00
-- url     : https://prove2.me/submissions/d3e135b1-0e54-4cab-93fd-d2973118eb9f

/- InternLM Lean-Workbook, lean_workbook_43899, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (p q r : Prop) : ((p ∨ q) ∧ (p → r) ∧ (q → r)) → r  := by
  first
  | solve
    | tauto
  | solve
    | intro h
      apply Or.elim (And.left h)
      intro hp
      apply (And.right h).left hp
      intro hq
      apply (And.right h).right hq
  | solve
    | refine' fun h ↦ Or.elim (And.left h) (fun hp ↦ (And.right h).left hp) (fun hq ↦ (And.right h).right hq)
  | solve
    | exact fun ⟨h₁, h₂, h₃⟩ ↦ h₁.elim h₂ h₃
  | solve
    | rintro ⟨h₁, h₂, h₃⟩
      cases' h₁ with hp hq <;> [apply h₂; apply h₃] <;> assumption
  | solve
    | refine' fun h => Or.elim h.left h.right.left h.right.right
  | solve
    | exact fun ⟨h₁, h₂, h₃⟩ ↦ Or.elim h₁ (fun hp ↦ h₂ hp) fun hq ↦ h₃ hq
  | solve
    | rintro ⟨h₁, h₂, h₃⟩
      cases h₁ <;> [apply h₂; apply h₃] <;> assumption
  | solve
    | refine fun h ↦ (h.1.elim h.2.1 h.2.2)
  | solve
    | exact fun ⟨h₁, h₂, h₃⟩ => h₁.elim (fun hp => h₂ hp) fun hq => h₃ hq
  | solve
    | intros h
      aesop
  | solve
    | intro h
      exact (h.left.elim (h.right.left) (h.right.right))
  | solve
    | exact by aesop
  | solve
    | intro h
      aesop
  | solve
    | intro h
      tauto
  | solve
    | refine' fun h => (h.1.elim h.2.1 h.2.2)
  | solve
    | exact fun h => (h.left.elim (fun hp => h.right.left hp) fun hq => h.right.right hq)
  | solve
    | rw [or_comm]
      tauto
  | solve
    | exact fun h ↦ Or.elim (And.left h) (fun hp ↦ (And.right h).left hp) (fun hq ↦ (And.right h).right hq)
  | solve
    | exact fun ⟨h₁, h₂, h₃⟩ ↦ h₁.elim (fun hp ↦ h₂ hp) fun hq ↦ h₃ hq
  | solve
    | rintro ⟨h₁, h₂, h₃⟩
      cases' h₁ with h₁ h₁
      apply h₂
      exact h₁
      apply h₃
      exact h₁
  | solve
    | rintro ⟨h, hp, hq⟩
      cases' h with hpq hpq <;> [apply hp; apply hq] <;> assumption
example : (∀ (p q r : Prop), ((p ∨ q) ∧ (p → r) ∧ (q → r)) → r) := @solution
#print axioms solution
