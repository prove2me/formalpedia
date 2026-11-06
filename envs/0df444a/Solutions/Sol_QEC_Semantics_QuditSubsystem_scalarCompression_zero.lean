-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.scalarCompression_zero
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T17:45:14.993628+00:00
-- url     : https://prove2.me/submissions/a5f73fee-339a-4c3c-acd9-b1a9b46ab3d5

-- ID: 203efa7b-b188-4e2a-9a0d-76dac60e8506 | NAME: QEC.Semantics.QuditSubsystem.scalarCompression_zero | 未本地编译验证
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open DensityOperator
open scoped BigOperators ComplexOrder TensorProduct
universe u v w
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}

theorem solution (C : QuantumCode (Qudit.QuditRegister q)) :
    ScalarCompression C (0 : Operator (Qudit.QuditRegister q)) := by
  refine ⟨0, ?_⟩
  ext x
  simp
