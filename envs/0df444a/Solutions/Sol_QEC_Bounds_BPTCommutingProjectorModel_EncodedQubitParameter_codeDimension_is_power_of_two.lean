-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.EncodedQubitParameter.codeDimension_is_power_of_two
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T17:50:01.295216+00:00
-- url     : https://prove2.me/submissions/351b2c07-7f69-4306-b92c-c49e731e6f09

-- ID: 908033de-7911-4dae-8818-0629bc0691db | NAME: QEC.Bounds.BPTCommutingProjectorModel.EncodedQubitParameter.codeDimension_is_power_of_two | 未本地编译验证
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

theorem solution
    {M : BPTCommutingProjectorModel L κ} (parameter : EncodedQubitParameter M) :
    ∃ k, M.codeSpace.dimension = 2 ^ k := by
  exact ⟨parameter.encodedQubits, parameter.codeDimension_eq_two_pow⟩
