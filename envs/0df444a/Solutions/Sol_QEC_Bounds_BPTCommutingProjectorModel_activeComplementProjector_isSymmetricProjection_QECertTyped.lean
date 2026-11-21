-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.activeComplementProjector_isSymmetricProjection_QECertTyped
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:59:49.960806+00:00
-- url     : https://prove2.me/submissions/3798e4a3-7449-46c2-98f6-56dcaf172761

import Definitions.Def_QEC_Import_Typed_5a24ac76332d0d9b
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyHelpers
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isSymmetricProjection_isometric_lift
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_linearIsometry_adjoint_comp_self


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 200000
namespace QEC.Bounds.BPTCommutingProjectorModel
private theorem qecertCompressionFrontier5a24ac76332d0d9b
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nC : Nat} [NeZero nC]
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC)))
    (P : Semantics.Operator (ActiveComplementDomain M region nC WC))
    (hP : @LinearMap.IsSymmetricProjection Complex
      (ActiveComplementDomain M region nC WC) _ _ _ P) :
    @LinearMap.IsSymmetricProjection Complex
      (ActiveComplementCodomain M region) _ _ _
      (M.activeComplementProjector region ccomponent WC UC P) := by
  let E := M.activeComplementEmbedding region ccomponent WC UC
  exact @isSymmetricProjection_isometric_lift
    (ActiveComplementDomain M region nC WC) (ActiveComplementCodomain M region)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    E.toLinearMap
    (@linearIsometry_adjoint_comp_self
      (ActiveComplementDomain M region nC WC) (ActiveComplementCodomain M region)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance E)
    P hP

theorem _root_.solution : QEC.Bounds.BPTCommutingProjectorModel.activeComplementProjector_isSymmetricProjection_QECertTypedStatement.{v} :=
  @qecertCompressionFrontier5a24ac76332d0d9b

end QEC.Bounds.BPTCommutingProjectorModel
