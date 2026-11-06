-- Prove2me | solution 2 for QEC.Bounds.BPTCommutingProjectorModel.EncodedQubitParameter.encodedQubits_eq_log2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:53:56.83552+00:00
-- url     : https://prove2.me/submissions/33ad151d-5fe1-45a1-a3da-82690f232d49

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
namespace EncodedQubitParameter
theorem _root_.solution
    {M : BPTCommutingProjectorModel L κ} (parameter : EncodedQubitParameter M) :
    Nat.log 2 M.codeSpace.dimension = parameter.encodedQubits := by
  rw [parameter.codeDimension_eq_two_pow]
  exact Nat.log_pow (by omega) parameter.encodedQubits
end EncodedQubitParameter
end QEC.Bounds.BPTCommutingProjectorModel
