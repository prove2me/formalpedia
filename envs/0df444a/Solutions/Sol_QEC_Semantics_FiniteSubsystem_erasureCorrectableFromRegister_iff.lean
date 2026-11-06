-- Prove2me | solution 1 for QEC.Semantics.FiniteSubsystem.erasureCorrectableFromRegister_iff
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T17:55:04.853439+00:00
-- url     : https://prove2.me/submissions/dcfa5028-a7e0-47d0-a88b-47028059b30b

-- ID: fc7c1bbd-7710-4346-8e44-c1007d617266 | NAME: QEC.Semantics.FiniteSubsystem.erasureCorrectableFromRegister_iff | 未本地编译验证
import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Semantics_Core_Subsystem
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u
open QEC.Semantics.FiniteSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem solution (S : FiniteSubsystem ι)
    (C : QuantumCode (Qubit.QubitRegister ι))
    (recovery : QuantumChannel S.complementSystem (Qubit.QubitRegister ι)) :
    S.ErasureCorrectableFromRegister C recovery ↔
      Correctable (Qubit.QubitRegister ι) S.complementSystem C
        S.erasureChannelFromRegister recovery := by
  rfl
