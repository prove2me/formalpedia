-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.erasureChannel_specification
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:45:56.400497+00:00
-- url     : https://prove2.me/submissions/5274739c-145b-462c-8270-4c8b88302840

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
    S.erasureChannel =
      QuantumChannel.comp
        (partialTraceRightRaw_cptp S.complementSystem S.selectedSystem)
        (QuantumChannel.unitaryConj S.factorSwap) :=
  rfl
end QEC.Semantics.QuditSubsystem
