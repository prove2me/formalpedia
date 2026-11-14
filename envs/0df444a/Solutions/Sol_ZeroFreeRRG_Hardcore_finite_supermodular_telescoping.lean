-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.finite_supermodular_telescoping
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:09:07.899772+00:00
-- url     : https://prove2.me/submissions/4396cbbb-26ed-4fa6-bb97-5d6af0546652

import Mathlib
set_option autoImplicit false
open scoped BigOperators

theorem solution {ι : Type} [DecidableEq ι] (v : Finset ι → ℝ)
    (hSM : ∀ S : Finset ι, ∀ i j, i ∉ S → j ∉ S → i ≠ j →
      v (insert i (insert j S)) + v S ≥ v (insert i S)+v (insert j S))
    (S : Finset ι) :
    v S ≥ v ∅ + ∑ i ∈ S, (v {i} - v ∅) := by
  have hmarg (S : Finset ι) (i : ι) (hi : i ∉ S) :
      v (insert i S)-v S ≥ v {i}-v ∅ := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert j S hj ih =>
      have hiS : i ∉ S := fun h => hi (Finset.mem_insert_of_mem h)
      have hij : i ≠ j := by
        intro h
        subst i
        exact hi (Finset.mem_insert_self _ _)
      have hind := ih hiS
      have h := hSM S i j hiS hj hij
      linarith
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have h := hmarg S i hi
    rw [Finset.sum_insert hi]
    linarith
