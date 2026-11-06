-- Prove2me | solution 2 for QEC.Bounds.BPTCommutingProjectorModel.EncodedQubitParameter.codeDimension_is_power_of_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:54:01.686337+00:00
-- url     : https://prove2.me/submissions/a3bb7ae3-a3fd-46a2-859f-6a219d9c5e65

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
    ∃ k, M.codeSpace.dimension = 2 ^ k :=
  ⟨parameter.encodedQubits, parameter.codeDimension_eq_two_pow⟩
end EncodedQubitParameter
end QEC.Bounds.BPTCommutingProjectorModel
