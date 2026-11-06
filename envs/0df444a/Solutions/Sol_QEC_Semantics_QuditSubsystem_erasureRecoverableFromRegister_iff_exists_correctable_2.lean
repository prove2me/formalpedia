-- Prove2me | solution 2 for QEC.Semantics.QuditSubsystem.erasureRecoverableFromRegister_iff_exists_correctable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:02:35.337296+00:00
-- url     : https://prove2.me/submissions/f460f4d5-e0da-4add-9542-f2e1a1eab02e

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
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution (S : QuditSubsystem q)
    (C : QuantumCode (Qudit.QuditRegister q)) :
    S.ErasureRecoverableFromRegister C ↔
      ∃ recovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q),
        Correctable (Qudit.QuditRegister q) S.complementSystem C
          S.erasureChannelFromRegister recovery :=
  Iff.rfl
end QEC.Semantics.QuditSubsystem
