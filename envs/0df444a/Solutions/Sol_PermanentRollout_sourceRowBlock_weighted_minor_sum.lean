-- Prove2me | solution 1 for PermanentRollout.sourceRowBlock_weighted_minor_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/96fd266f-e135-4e56-b355-d7051ded7083

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_sourceRowBlock_powersetCard_eq_filter

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    {R : Type*} [CommSemiring R]
    (b t s d : ℕ) (X : Matrix (Fin (b * t)) (Fin s) R)
    (weight : Fin b → R) :
    (∑ omitted ∈ (Finset.univ : Finset (Fin (b * t))).powersetCard d,
      (∑ h : Fin b,
        if omitted ⊆ sourceRowBlock b t h then weight h else 0) *
        ∑ columns ∈ (Finset.univ : Finset (Fin s)).powersetCard d,
          sourceBlockMinor (b * t) s X omitted columns) =
      ∑ h : Fin b, weight h * sourceRowBlockMinorSum b t s d X h := by
  classical
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  unfold sourceRowBlockMinorSum
  rw [sourceRowBlock_powersetCard_eq_filter b t d h]
  simp [Finset.sum_filter, Finset.mul_sum, ite_mul]
end PermanentRollout
