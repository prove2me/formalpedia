-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.fullCodeProjector_idempotent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:06:33.376321+00:00
-- url     : https://prove2.me/submissions/dc47cdd6-36aa-47b9-babf-0ea1631c7a8b

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
theorem _root_.solution (M : BPTCommutingProjectorModel L κ) :
    M.fullCodeProjector.comp M.fullCodeProjector = M.fullCodeProjector :=
  M.codeSpace.projector_idempotent
end QEC.Bounds.BPTCommutingProjectorModel
