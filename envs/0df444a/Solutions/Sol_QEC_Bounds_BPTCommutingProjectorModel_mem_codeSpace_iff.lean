-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.mem_codeSpace_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:31:55.45512+00:00
-- url     : https://prove2.me/submissions/367d6d64-6a36-4874-ae46-23b1065d2fb1

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
theorem _root_.solution (M : BPTCommutingProjectorModel L κ) (vector : L.Register) :
    vector ∈ M.codeSpace.carrier ↔ ∀ check, M.projector check vector = vector :=
  Iff.rfl
end QEC.Bounds.BPTCommutingProjectorModel
