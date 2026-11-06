-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.fullCodeProjector_fixed_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:08:23.397194+00:00
-- url     : https://prove2.me/submissions/8ed08e54-40d5-4182-9a7f-903643e0edec

import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_codeSpace_iff
import Theorems.Thm_QEC_Semantics_QuantumCode_projector_eq_self_iff_mem


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
theorem _root_.solution (M : BPTCommutingProjectorModel L κ)
    (vector : L.Register) :
    M.fullCodeProjector vector = vector ↔ ∀ check, M.projector check vector = vector := by
  rw [show M.fullCodeProjector = M.codeSpace.projector from rfl,
    M.codeSpace.projector_eq_self_iff_mem]
  exact M.mem_codeSpace_iff vector
end QEC.Bounds.BPTCommutingProjectorModel
