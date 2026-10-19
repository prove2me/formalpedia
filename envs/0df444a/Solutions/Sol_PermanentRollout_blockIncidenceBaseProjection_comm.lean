-- Prove2me | solution 1 for PermanentRollout.blockIncidenceBaseProjection_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/4a7a930b-c37a-4ea0-84d4-0f69d32aaf92

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_blockIncidenceSingleBlockInclusion_mk

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    (b t s d : ℕ) (block : Fin b) :
    (blockIncidenceBaseProjection b t s d).comp
        (MvPolynomial.rename
          (fun z : IncidenceRowBlock t ⊕ (Fin s × Fin (d - 2)) =>
            (block, z))) =
      (blockIncidenceSingleBlockInclusion b t s d block).comp
        (partitionIncidenceGlobalBaseProjection t s d) := by
  ext z
  rcases z with z | ⟨column, index⟩
  · simp only [AlgHom.comp_apply, MvPolynomial.rename_X,
      blockIncidenceBaseProjection, partitionIncidenceGlobalBaseProjection,
      MvPolynomial.aeval_X]
    change
      Ideal.Quotient.mk (blockIncidenceIdeal b t s d)
          (MvPolynomial.X (block, Sum.inl z)) =
        blockIncidenceSingleBlockInclusion b t s d block
          (Ideal.Quotient.mk (partitionIncidenceIdeal t s d)
            (MvPolynomial.X (Sum.inl z)))
    rw [blockIncidenceSingleBlockInclusion_mk]
    simp
  · simp only [AlgHom.comp_apply, MvPolynomial.rename_X,
      blockIncidenceBaseProjection, partitionIncidenceGlobalBaseProjection,
      MvPolynomial.aeval_X]
    change
      Ideal.Quotient.mk (blockIncidenceIdeal b t s d)
        (MvPolynomial.rename
          (fun row : Fin t => (block, Sum.inr (column, row)))
          (partitionFiberCoordinateEsymmPolynomial t (index.val + 1))) =
        blockIncidenceSingleBlockInclusion b t s d block
          (Ideal.Quotient.mk (partitionIncidenceIdeal t s d)
            (MvPolynomial.rename
              (fun row : Fin t => Sum.inr (column, row))
              (partitionFiberCoordinateEsymmPolynomial t (index.val + 1))))
    rw [blockIncidenceSingleBlockInclusion_mk,
      MvPolynomial.rename_rename]
    rfl
end PermanentRollout
