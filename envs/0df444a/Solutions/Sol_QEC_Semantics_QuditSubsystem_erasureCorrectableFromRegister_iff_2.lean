-- Prove2me | solution 2 for QEC.Semantics.QuditSubsystem.erasureCorrectableFromRegister_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:02:23.688271+00:00
-- url     : https://prove2.me/submissions/edc04e1b-5e00-4879-9179-9ede57856f3c

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
    (C : QuantumCode (Qudit.QuditRegister q))
    (recovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q)) :
    S.ErasureCorrectableFromRegister C recovery ↔
      Correctable (Qudit.QuditRegister q) S.complementSystem C
        S.erasureChannelFromRegister recovery :=
  Iff.rfl
end QEC.Semantics.QuditSubsystem
