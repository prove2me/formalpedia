-- Prove2me | solution 2 for QEC.Semantics.QuditSubsystem.erasureChannelFromRegister_specification
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:02:02.174219+00:00
-- url     : https://prove2.me/submissions/c5ec0dbc-6371-4f70-bad9-c178f71839b9

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
theorem _root_.solution (S : QuditSubsystem q) :
    S.erasureChannelFromRegister =
      QuantumChannel.comp S.erasureChannel
        (QuantumChannel.unitaryConj S.registerFactorization) :=
  rfl
end QEC.Semantics.QuditSubsystem
