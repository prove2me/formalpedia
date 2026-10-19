-- Prove2me | solution 1 for PermanentRollout.sourceBlockMatchingExpansion_eq_sum_glued_fibres
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/3ba516fc-69a7-46b6-9968-75b456603fc4

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_sourceBlockGluedFibre_eq

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace PermanentRollout
theorem _root_.solution
    {R : Type*} [CommSemiring R] (r s d : ℕ)
    (X : Matrix (Fin r) (Fin s) R)
    (U : Matrix (Fin r) (Fin (r - d)) R) :
    sourceBlockMatchingExpansion r s d X U =
      ∑ I ∈ (Finset.univ : Finset (Fin r)).powersetCard d,
        ∑ J ∈ (Finset.univ : Finset (Fin s)).powersetCard d,
          sourceBlockGluedFibre r s d X U I J := by
  unfold sourceBlockMatchingExpansion
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  exact (sourceBlockGluedFibre_eq r s d X U I J
    (Finset.mem_powersetCard.mp hJ).2).symm
end PermanentRollout
