-- Prove2me | solution 1 for WorkbookSyntax.plus_44891
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:02:38.662112+00:00
-- url     : https://prove2.me/submissions/09033952-70cd-4c1d-88ba-f327203e20f6

/- InternLM Lean-Workbook, Apache-2.0. The obsolete finite-sum binder syntax is explicitly modernized. -/
import Mathlib
open Nat
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 100000
theorem solution (A B : ℕ) (hA : A = ∑ i ∈ Finset.filter (λ x => x % 3 = 1) (Finset.Icc 1 2011), i) (hB : B = ∑ i ∈ Finset.filter (λ x => x % 3 = 2) (Finset.Icc 1 2011), i) : A - B = 1341   := by
  subst A; subst B
  decide +kernel
example : (∀ (A B : ℕ) (hA : A = ∑ i ∈ Finset.filter (λ x => x % 3 = 1) (Finset.Icc 1 2011), i) (hB : B = ∑ i ∈ Finset.filter (λ x => x % 3 = 2) (Finset.Icc 1 2011), i), A - B = 1341) := @solution
#print axioms solution
