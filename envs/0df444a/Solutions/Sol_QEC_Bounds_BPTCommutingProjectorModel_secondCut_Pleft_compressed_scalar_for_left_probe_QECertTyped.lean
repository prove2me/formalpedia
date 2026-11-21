-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.secondCut_Pleft_compressed_scalar_for_left_probe_QECertTyped
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:40:31.802553+00:00
-- url     : https://prove2.me/submissions/fba92153-ed47-44ef-ba98-54c24eaf2e5c

import Definitions.Def_QEC_Import_Typed_a360fd0a9c529c33
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_Coordinates
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftProbe
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCut_compressed_scalar_for_left_subtype_probe_QECertChecked


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 300000
namespace QEC.Bounds.BPTCommutingProjectorModel
private theorem qecertSecondCutLeftProbea360fd0a9c529c33
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hM : M.RegionErasureRecoverable region)
    (H W0 : Submodule Complex (M.fourFactorB region))
    {n : Nat} [NeZero n]
    (J : Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) H)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) →ₗ[Complex]
      Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)))
    (hJ : J = tensorTripleSubtypeEmbedding (A := M.fourFactorA region)
      (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) H)
    (Rcompressed : Semantics.Operator
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) H)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))))
    (hreconstruct : M.secondCutCodeLift region =
      J.comp (Rcompressed.comp (LinearMap.adjoint J)))
    (U : Semantics.UnitaryTransport H
      (Semantics.CompositeSystem W0 (isotypicLiftedMultiplicity.{0} n)))
    (X : Semantics.Operator (Semantics.CompositeSystem (M.fourFactorA region) W0)) :
    ∃ scalar : Complex,
      Rcompressed *
          overlapLiftLeft
            (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
            ((unitaryLTensor (M.fourFactorA region) U).symm.conjOperator
              (rightTensorExtensionAfterLeft (M.fourFactorA region) W0
                (isotypicLiftedMultiplicity.{0} n) X)) *
          Rcompressed =
        scalar • Rcompressed := by
    let Esub : Semantics.Operator (Semantics.CompositeSystem (M.fourFactorA region) H) :=
      (unitaryLTensor (M.fourFactorA region) U).symm.conjOperator
        (rightTensorExtensionAfterLeft (M.fourFactorA region)
          W0 (isotypicLiftedMultiplicity.{0} n) X)
    rcases M.secondCut_compressed_scalar_for_left_subtype_probe_QECertChecked
      region hM H J hJ Rcompressed hreconstruct Esub with ⟨scalar, hscalar⟩
    exact ⟨scalar, hscalar⟩

theorem _root_.solution : QEC.Bounds.BPTCommutingProjectorModel.secondCut_Pleft_compressed_scalar_for_left_probe_QECertTypedStatement.{v} :=
  @qecertSecondCutLeftProbea360fd0a9c529c33

end QEC.Bounds.BPTCommutingProjectorModel
