-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.projector_supported_on
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:08:21.736385+00:00
-- url     : https://prove2.me/submissions/926c7d90-bca6-4d4b-91a2-79383da4ec11

import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Theorems.Thm_QEC_Semantics_QuditSubsystem_extendLocalToRegister_operatorSupportedOn


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
    (L.subsystem (M.support check)).OperatorSupportedOnRegister (M.projector check) := by
  exact (L.subsystem (M.support check)).extendLocalToRegister_operatorSupportedOn
    (M.localProjector check)
end QEC.Bounds.BPTCommutingProjectorModel
