-- Prove2me | solution 1 for QEC.Semantics.FiniteSubsystem.erasureRecoverableFromRegister_iff_exists_correctable
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T17:56:07.795552+00:00
-- url     : https://prove2.me/submissions/f932e02c-42f6-4944-8177-55322efa866a

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
    (C : QuantumCode (Qubit.QubitRegister ι)) :
    S.ErasureRecoverableFromRegister C ↔
      ∃ recovery : QuantumChannel S.complementSystem (Qubit.QubitRegister ι),
        Correctable (Qubit.QubitRegister ι) S.complementSystem C
          S.erasureChannelFromRegister recovery := by
  solve | rfl | simp [QubitRegister, FiniteSubsystem, complementSystem, erasureChannelFromRegister, ErasureRecoverableFromRegister] | simp_all [QubitRegister, FiniteSubsystem, complementSystem, erasureChannelFromRegister, ErasureRecoverableFromRegister] | omega | norm_num
