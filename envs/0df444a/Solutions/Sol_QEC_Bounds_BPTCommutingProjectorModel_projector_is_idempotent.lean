-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.projector_is_idempotent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:31:50.729898+00:00
-- url     : https://prove2.me/submissions/ba2565b3-ce06-4ab9-b3d2-e6a9e83f03fc

import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Theorems.Thm_QEC_Semantics_QuantumCode_projector_idempotent


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
    (M.projector check).comp (M.projector check) = M.projector check :=
  M.projector_idempotent check
end QEC.Bounds.BPTCommutingProjectorModel
