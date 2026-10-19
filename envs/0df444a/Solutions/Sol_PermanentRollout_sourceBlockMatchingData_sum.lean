-- Prove2me | solution 1 for PermanentRollout.sourceBlockMatchingData_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/055d5540-071e-404f-993d-0bf6a7f2f9b7

import Mathlib
import Definitions.Def_Permanent

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
    (∑ data : SourceBlockMatchingData r s d,
      sourceBlockMatchingWeight r s d X U
        (sourceBlockDataMatching r s d data)) =
      ∑ I ∈ (Finset.univ : Finset (Fin r)).powersetCard d,
        ∑ J ∈ (Finset.univ : Finset (Fin s)).powersetCard d,
          sourceBlockGluedFibre r s d X U I J := by
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type,
    sourceBlockDataMatching, sourceBlockMatchingWeight]
  let rowSet : Finset (Finset (Fin r)) :=
    (Finset.univ : Finset (Fin r)).powersetCard d
  let columnSet : Finset (Finset (Fin s)) :=
    (Finset.univ : Finset (Fin s)).powersetCard d
  let rowFibre : Finset (Fin r) → R :=
    fun I => ∑ J : columnSet, sourceBlockGluedFibre r s d X U I J.val
  change
    (∑ I : rowSet, rowFibre I.val) =
      ∑ I ∈ rowSet,
        ∑ J ∈ columnSet,
          sourceBlockGluedFibre r s d X U I J
  rw [Finset.sum_coe_sort rowSet rowFibre]
  apply Finset.sum_congr rfl
  intro I hI
  exact Finset.sum_coe_sort columnSet
    (fun J => sourceBlockGluedFibre r s d X U I J)
end PermanentRollout
