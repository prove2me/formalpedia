-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.erasureCorrectableFromRegister_iff
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T17:56:31.714752+00:00
-- url     : https://prove2.me/submissions/887c4f9e-5c38-4e9e-b0f1-35cf2a5d4ad9

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

theorem solution (S : QuditSubsystem q)
    (C : QuantumCode (Qudit.QuditRegister q))
    (recovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q)) :
    S.ErasureCorrectableFromRegister C recovery ↔
      Correctable (Qudit.QuditRegister q) S.complementSystem C
        S.erasureChannelFromRegister recovery := by
  solve | rfl | simp [QuditRegister, QuditSubsystem, complementSystem, erasureChannelFromRegister, ErasureCorrectableFromRegister] | simp_all [QuditRegister, QuditSubsystem, complementSystem, erasureChannelFromRegister, ErasureCorrectableFromRegister] | omega | norm_num
