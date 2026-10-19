-- Prove2me | solution 1 for PermanentRollout.sourceBlockMatrix_permanent_eq_matchingExpansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/ef16e83b-c6e9-4ea3-8051-dcb0a7a9dee6

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_sourceBlockMatchingExpansion_eq_sum_glued_fibres
import Theorems.Thm_PermanentRollout_sourceBlockMatrix_permanent_eq_valid_sum
import Theorems.Thm_PermanentRollout_sourceBlockMatchingData_sum

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace PermanentRollout
theorem _root_.solution
    {R : Type*} [CommSemiring R] (r s d : ℕ) (hr : d ≤ r)
    (X : Matrix (Fin r) (Fin s) R)
    (U : Matrix (Fin r) (Fin (r - d)) R) :
    rectangularPermanent (sourceBlockMatrix r s d X U) =
      sourceBlockMatchingExpansion r s d X U := by
  calc
    rectangularPermanent (sourceBlockMatrix r s d X U) =
        ∑ matching : SourceBlockValidMatching r s d,
          sourceBlockMatchingWeight r s d X U matching.val :=
      sourceBlockMatrix_permanent_eq_valid_sum r s d X U
    _ = ∑ data : SourceBlockMatchingData r s d,
          sourceBlockMatchingWeight r s d X U
            (sourceBlockDataMatching r s d data) := by
      symm
      exact Fintype.sum_equiv
        (sourceBlockMatchingDataEquiv r s d hr)
        (fun data : SourceBlockMatchingData r s d =>
          sourceBlockMatchingWeight r s d X U
            (sourceBlockDataMatching r s d data))
        (fun matching : SourceBlockValidMatching r s d =>
          sourceBlockMatchingWeight r s d X U matching.val)
        (fun _ => rfl)
    _ = ∑ I ∈ (Finset.univ : Finset (Fin r)).powersetCard d,
          ∑ J ∈ (Finset.univ : Finset (Fin s)).powersetCard d,
            sourceBlockGluedFibre r s d X U I J :=
      sourceBlockMatchingData_sum r s d X U
    _ = sourceBlockMatchingExpansion r s d X U :=
      (sourceBlockMatchingExpansion_eq_sum_glued_fibres r s d X U).symm
end PermanentRollout
