-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.extendLocal_operatorSupportedOn
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T17:46:50.323722+00:00
-- url     : https://prove2.me/submissions/7281f270-7f09-44dd-b47a-b583dc4e476e

-- ID: 05d52e3a-19f4-42c3-b9d8-0c64985971cc | NAME: QEC.Semantics.QuditSubsystem.extendLocal_operatorSupportedOn | 未本地编译验证
import Definitions.Def_QEC_Semantics_Channels_Core
import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}

theorem solution (S : QuditSubsystem q) (A : Operator S.selectedSystem) :
    S.OperatorSupportedOn (S.extendLocal A) := by
  exact ⟨A, rfl⟩
