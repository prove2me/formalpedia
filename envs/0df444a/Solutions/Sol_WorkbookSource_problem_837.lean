-- Prove2me | solution 1 for WorkbookSource.problem_837
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:15:07.912947+00:00
-- url     : https://prove2.me/submissions/65236339-33a9-425d-a469-7d749b28352a

/- InternLM Lean-Workbook, lean_workbook_837, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution :∀ a b c x y z p q r : ℝ,  p = a^2 + b^2 + c^2 ∧ q = a * b + b * c + c * a ∧ r = (b - a) * (b - c) ∧ x = a^2 + 2 * b * c ∧ y = b^2 + 2 * c * a ∧ z = c^2 + 2 * a * b → x * z = p * (q - r) + r^2  := by
  first
  | solve
    | rintro a b c x y z p q r ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
      ring
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | rintro a b c x y z p q r ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      ring
  | solve
    | intro a b c x y z p q r
      rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      ring
  | solve
    | intros a b c x y z p q r h
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
      ring
  | solve
    | intro a b c x y z p q r h
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
      ring_nf
example : (∀ a b c x y z p q r : ℝ,  p = a^2 + b^2 + c^2 ∧ q = a * b + b * c + c * a ∧ r = (b - a) * (b - c) ∧ x = a^2 + 2 * b * c ∧ y = b^2 + 2 * c * a ∧ z = c^2 + 2 * a * b → x * z = p * (q - r) + r^2) := @solution
#print axioms solution
