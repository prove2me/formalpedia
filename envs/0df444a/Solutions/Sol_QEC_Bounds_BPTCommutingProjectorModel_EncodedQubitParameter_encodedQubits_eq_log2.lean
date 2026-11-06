-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.EncodedQubitParameter.encodedQubits_eq_log2
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T18:10:10.692385+00:00
-- url     : https://prove2.me/submissions/39f9d781-fc41-4bd3-8a0f-da1e900662de

-- ID: 510fb2b1-5e2f-41ac-b89f-35f19fe5d1ce | NAME: QEC.Bounds.BPTCommutingProjectorModel.EncodedQubitParameter.encodedQubits_eq_log2 | 未本地编译验证
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
    Nat.log 2 M.codeSpace.dimension = parameter.encodedQubits := by
  rw [parameter.codeDimension_eq_two_pow]
  simp
