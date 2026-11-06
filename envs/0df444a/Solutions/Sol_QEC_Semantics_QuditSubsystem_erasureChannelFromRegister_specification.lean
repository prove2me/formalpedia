-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.erasureChannelFromRegister_specification
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T17:49:52.404029+00:00
-- url     : https://prove2.me/submissions/402aa6a0-0537-4c98-a8b9-8011efec331c

-- ID: 062ff0f0-80dd-4d64-b925-f64903de2064 | NAME: QEC.Semantics.QuditSubsystem.erasureChannelFromRegister_specification | 未本地编译验证
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

theorem solution (S : QuditSubsystem q) :
    S.erasureChannelFromRegister =
      QuantumChannel.comp S.erasureChannel
        (QuantumChannel.unitaryConj S.registerFactorization) := by
  rfl
