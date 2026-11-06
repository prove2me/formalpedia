-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.projector_adjoint_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:06:17.747652+00:00
-- url     : https://prove2.me/submissions/e9eafccd-bc10-4ce4-a67f-127ae7d4284f

import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {κ : Type v} [Fintype κ]
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution (M : BPTCommutingProjectorModel L κ) (check : κ) :
    LinearMap.adjoint (M.projector check) = M.projector check :=
  M.projector_self_adjoint check
end QEC.Bounds.BPTCommutingProjectorModel
