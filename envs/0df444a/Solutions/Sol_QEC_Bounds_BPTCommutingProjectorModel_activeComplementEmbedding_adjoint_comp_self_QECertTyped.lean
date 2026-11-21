-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.activeComplementEmbedding_adjoint_comp_self_QECertTyped
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:52:08.9152+00:00
-- url     : https://prove2.me/submissions/1cd3f88a-dd6a-4dcc-9451-6514387a44c0

import Definitions.Def_QEC_Import_Typed_b22afd9577f25d66
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyHelpers
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
private theorem qecertCompressionFrontierb22afd9577f25d66
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nC : Nat} [NeZero nC]
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC))) :
    let E := M.activeComplementEmbedding region ccomponent WC UC
    (LinearMap.adjoint E.toLinearMap).comp E.toLinearMap =
      (1 : Semantics.Operator
        (ActiveComplementDomain M region nC WC)) := by
  dsimp only
  exact @linearIsometry_adjoint_comp_self
    (ActiveComplementDomain M region nC WC) (ActiveComplementCodomain M region)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (M.activeComplementEmbedding region ccomponent WC UC)

theorem _root_.solution : QEC.Bounds.BPTCommutingProjectorModel.activeComplementEmbedding_adjoint_comp_self_QECertTypedStatement.{v} :=
  @qecertCompressionFrontierb22afd9577f25d66

end QEC.Bounds.BPTCommutingProjectorModel
