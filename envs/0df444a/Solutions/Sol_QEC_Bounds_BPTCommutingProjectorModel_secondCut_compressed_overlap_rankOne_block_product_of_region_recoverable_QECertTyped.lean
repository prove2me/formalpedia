-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.secondCut_compressed_overlap_rankOne_block_product_of_region_recoverable_QECertTyped
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:04:49.356998+00:00
-- url     : https://prove2.me/submissions/75ca00a4-19fb-4cb9-aff8-3e723f07246e

import Definitions.Def_QEC_Import_Typed_2cc4628e6db81964
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftRankOneWitness
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftRankOneBlock
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCut_Pleft_eq_rankOne_of_region_recoverable_QECertTyped
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCut_compressed_overlap_block_product_QECertChecked


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
private theorem qecertSecondCutRankOneProduct2cc4628e6db81964
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (hM : M.RegionErasureRecoverable region)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    {n : Nat} [NeZero n]
    (W : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (U : Semantics.UnitaryTransport (component.1.restrictScalars Complex)
      (Semantics.CompositeSystem (W.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} n)))
    (Pleft : Semantics.Operator
      (Semantics.CompositeSystem (M.fourFactorA region) (W.restrictScalars Complex)))
    (Qright : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} n)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))))
    (hsource : SecondCutActiveBlockConditions M region component W U Pleft Qright) :
    SecondCutRankOneBlockProduct M region component W U Qright := by
  unfold SecondCutActiveBlockConditions at hsource
  rcases hsource with ⟨hactive, hleft, hright⟩
  unfold SecondCutRankOneBlockProduct
  rcases M.secondCut_Pleft_eq_rankOne_of_region_recoverable_QECertTyped
    region hcode hM component W U Pleft Qright hactive hleft hright with
    ⟨phi, hphi, hPleft⟩
  refine ⟨phi, hphi, ?_⟩
  calc
    _ = TensorProduct.map Pleft Qright :=
      M.secondCut_compressed_overlap_block_product_QECertChecked
        region component W U Pleft Qright hleft hright
    _ = TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap Qright :=
      congrArg (fun left => TensorProduct.map left Qright) hPleft

theorem _root_.solution : QEC.Bounds.BPTCommutingProjectorModel.secondCut_compressed_overlap_rankOne_block_product_of_region_recoverable_QECertTypedStatement.{v} :=
  @qecertSecondCutRankOneProduct2cc4628e6db81964

end QEC.Bounds.BPTCommutingProjectorModel
