-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.secondCut_active_sector_tensor_blocks_of_nonzero_code
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:10:04.57441+00:00
-- url     : https://prove2.me/submissions/8ccf299f-2c3e-4d44-bd36-98cdc6aa24af

import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Selection
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutProjectorAB_isSymmetric
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCut_overlap_commute
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCut_exists_unique_active_leftIsotypicSector_of_nonzero_code
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_overlapProjectorTensorBlockFactorization_of_commuting


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 800000
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (hM : M.RegionErasureRecoverable region) :
    ∃ component : isotypicComponents
        (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
        (M.fourFactorB region),
      M.secondCutCodeLift region * M.secondCutSectorLift region component =
          M.secondCutCodeLift region ∧
      (∀ other : isotypicComponents
          (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
          (M.fourFactorB region),
        other ≠ component →
        M.secondCutCodeLift region * M.secondCutSectorLift region other = 0) ∧
      OverlapProjectorTensorBlockFactorization
        (M.fourFactorProjectorABLocal region) (M.secondCutProjectorBbarM region) component := by
  rcases M.secondCut_exists_unique_active_leftIsotypicSector_of_nonzero_code
    region hcode hM with ⟨component, hactive, hother⟩
  have hself : LinearMap.adjoint (M.fourFactorProjectorABLocal region) =
      M.fourFactorProjectorABLocal region := by
    apply LinearMap.isSelfAdjoint_iff'.mp
    exact (LinearMap.isSymmetric_iff_isSelfAdjoint _).mp
      (M.secondCutProjectorAB_isSymmetric region)
  have hover : Commute
      (overlapLiftLeft
        (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
        (M.fourFactorProjectorABLocal region))
      (overlapLiftRight (A := M.fourFactorA region)
        (M.secondCutProjectorBbarM region)) :=
    M.secondCut_overlap_commute region
  exact ⟨component, hactive, hother,
    overlapProjectorTensorBlockFactorization_of_commuting
      (M.fourFactorProjectorABLocal region) (M.secondCutProjectorBbarM region)
      hself hover component⟩
end QEC.Bounds.BPTCommutingProjectorModel
