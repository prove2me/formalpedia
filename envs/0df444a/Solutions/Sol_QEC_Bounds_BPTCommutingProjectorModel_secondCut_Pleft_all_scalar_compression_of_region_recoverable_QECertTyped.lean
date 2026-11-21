-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.secondCut_Pleft_all_scalar_compression_of_region_recoverable_QECertTyped
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:25:34.195004+00:00
-- url     : https://prove2.me/submissions/c3c3b186-e127-487e-b1c4-f44ff8768624

import Definitions.Def_QEC_Import_Typed_c08eabc0d97f67cb
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftProbe
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftPhysical
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_left_factor_scalar_compression_of_tensor_block
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutCodeLift_eq_active_embedding_compression_of_absorption_QECertChecked
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCut_Pleft_compressed_scalar_for_left_probe_QECertTyped
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCut_Pleft_left_probe_transport
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCut_Qright_idempotent_and_ne_zero_of_nonzero_code_QECertTyped
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
set_option maxHeartbeats 12000000
namespace QEC.Bounds.BPTCommutingProjectorModel
private theorem qecertPleftAllScalarc08eabc0d97f67cb
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (hM : M.RegionErasureRecoverable region)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    {n : Nat} [NeZero n]
    (W : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region)) :
    let A := M.fourFactorA region
    let H := component.1.restrictScalars Complex
    let W0 := W.restrictScalars Complex
    let N := isotypicLiftedMultiplicity.{0} n
    let CD := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)
    ∀ (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W0 N))
      (Pleft : Semantics.Operator (Semantics.CompositeSystem A W0))
      (Qright : Semantics.Operator (Semantics.CompositeSystem N CD)),
      M.secondCutCodeLift region * M.secondCutSectorLift region component =
          M.secondCutCodeLift region →
      (unitaryLTensor A U).conjOperator
          (overlapProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) component) =
          rightTensorExtensionAfterLeft A W0 N Pleft →
      (unitaryRTensor U CD).conjOperator
          (overlapRightProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) (M.secondCutProjectorBbarM region) component) =
          leftTensorExtensionBeforeRight W0 N CD Qright →
      ∀ X : Semantics.Operator (Semantics.CompositeSystem A W0),
        ∃ scalar : Complex, Pleft * X * Pleft = scalar • Pleft := by
  intro A H W0 N CD U Pleft Qright hactive hleft hright
  let T := isotypicSectorBlockTransportLeft A H W0 N CD U
  have hQright : Qright * Qright = Qright ∧ Qright ≠ 0 := by
    exact M.secondCut_Qright_idempotent_and_ne_zero_of_nonzero_code_QECertTyped
      region hcode component W U Pleft Qright hactive hleft hright
  obtain ⟨hQidem, hQright0⟩ := hQright
  let J := tensorTripleSubtypeEmbedding (A := A) (C := CD) H
  have hJ : J = tensorTripleSubtypeEmbedding (A := A) (C := CD) H := rfl
  let Rcompressed : Semantics.Operator
      (Semantics.CompositeSystem (Semantics.CompositeSystem A H) CD) :=
    (LinearMap.adjoint J).comp ((M.secondCutCodeLift region).comp J)
  have hreconstruct : M.secondCutCodeLift region =
      J.comp (Rcompressed.comp (LinearMap.adjoint J)) := by
    exact M.secondCutCodeLift_eq_active_embedding_compression_of_absorption_QECertChecked
      region component hactive
  intro X
  let Lprobe := overlapLiftLeft (C := CD)
    ((unitaryLTensor A U).symm.conjOperator
      (rightTensorExtensionAfterLeft A W0 N X))
  rcases M.secondCut_Pleft_compressed_scalar_for_left_probe_QECertTyped
    region hM H W0 J hJ Rcompressed hreconstruct U X with ⟨scalar, hcompressedScalar⟩
  have hblock : T.conjOperator Rcompressed = TensorProduct.map Pleft Qright := by
    exact M.secondCut_compressed_overlap_block_product_QECertChecked
      region component W U Pleft Qright hleft hright
  have hprobe : T.conjOperator Lprobe =
      TensorProduct.map X (1 : Semantics.Operator (Semantics.CompositeSystem N CD)) := by
    exact M.secondCut_Pleft_left_probe_transport region H W0 U X
  refine ⟨scalar, ?_⟩
  exact left_factor_scalar_compression_of_tensor_block
    T Pleft Qright Rcompressed Lprobe X scalar hblock hQidem hQright0
      hcompressedScalar hprobe

theorem _root_.solution : QEC.Bounds.BPTCommutingProjectorModel.secondCut_Pleft_all_scalar_compression_of_region_recoverable_QECertTypedStatement.{v} :=
  @qecertPleftAllScalarc08eabc0d97f67cb

end QEC.Bounds.BPTCommutingProjectorModel
