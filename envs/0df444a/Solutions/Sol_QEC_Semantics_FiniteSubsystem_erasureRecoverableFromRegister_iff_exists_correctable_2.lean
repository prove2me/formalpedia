-- Prove2me | solution 2 for QEC.Semantics.FiniteSubsystem.erasureRecoverableFromRegister_iff_exists_correctable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:00:03.199105+00:00
-- url     : https://prove2.me/submissions/a5b21d32-ee97-47ab-b83b-3ad2b684d916

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
    (C : QuantumCode (Qubit.QubitRegister ι)) :
    S.ErasureRecoverableFromRegister C ↔
      ∃ recovery : QuantumChannel S.complementSystem (Qubit.QubitRegister ι),
        Correctable (Qubit.QubitRegister ι) S.complementSystem C
          S.erasureChannelFromRegister recovery :=
  Iff.rfl
end QEC.Semantics.FiniteSubsystem
