-- Prove2me | solution 2 for QEC.Semantics.FiniteSubsystem.erasureCorrectableFromRegister_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:59:50.005405+00:00
-- url     : https://prove2.me/submissions/7839126e-c583-4b9c-b479-5f3a1a02cf14

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
namespace QEC.Semantics.FiniteSubsystem
theorem _root_.solution (S : FiniteSubsystem ι)
    (C : QuantumCode (Qubit.QubitRegister ι))
    (recovery : QuantumChannel S.complementSystem (Qubit.QubitRegister ι)) :
    S.ErasureCorrectableFromRegister C recovery ↔
      Correctable (Qubit.QubitRegister ι) S.complementSystem C
        S.erasureChannelFromRegister recovery :=
  Iff.rfl
end QEC.Semantics.FiniteSubsystem
