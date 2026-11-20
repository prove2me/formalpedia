-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.encodedQubits_le_squarePartition_complement_log_dimensions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:36:35.7154+00:00
-- url     : https://prove2.me/submissions/246a6127-c9e2-4110-82fd-ae91891d1bc7

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_BlockRecursion
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_SquarePartition
import Theorems.Thm_QEC_Bounds_BPTSquareLattice_squarePartition_pairwise_disjoint
import Theorems.Thm_QEC_Bounds_BPTEntropy_bpt_encodedQubits_le_complement_log_dimensions


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open Semantics
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution
    (M : BPTCommutingProjectorModel L kappa)
    (parameter : BPTCommutingProjectorModel.EncodedQubitParameter M)
    (blockWidth margin : Nat)
    (hA : M.RegionErasureRecoverable (L.lattice.squarePartitionA blockWidth margin))
    (hB : M.RegionErasureRecoverable (L.lattice.squarePartitionB blockWidth margin)) :
    (parameter.encodedQubits : Real) <=
      ∑ i : (_root_.QEC.Bounds.BPTEntropy.QuditSubsystem.unionSubsystem
        (M.regionSubsystem (L.lattice.squarePartitionA blockWidth margin))
        (M.regionSubsystem (L.lattice.squarePartitionB blockWidth margin))).ComplementCoordinates,
        Real.logb 2 (L.localDimension i : Real) := by
  rcases hA with ⟨recoveryA, hcorrectA⟩
  rcases hB with ⟨recoveryB, hcorrectB⟩
  exact BPTEntropy.bpt_encodedQubits_le_complement_log_dimensions M parameter
    (L.lattice.squarePartitionA blockWidth margin)
    (L.lattice.squarePartitionB blockWidth margin)
    (L.lattice.squarePartition_pairwise_disjoint blockWidth margin).1
    recoveryA hcorrectA recoveryB hcorrectB
end QEC.Bounds.BPTCommutingProjectorModel
