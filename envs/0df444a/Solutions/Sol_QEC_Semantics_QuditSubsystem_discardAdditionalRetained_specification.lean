-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.discardAdditionalRetained_specification
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:02:13.330607+00:00
-- url     : https://prove2.me/submissions/67810de0-c8fe-42dc-be5a-029a0e95fe83

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
theorem _root_.solution (S T : QuditSubsystem q)
    (hST : S.selected ⊆ T.selected) :
    S.discardAdditionalRetained T hST =
      QuantumChannel.comp
        (partialTraceRightRaw_cptp T.complementSystem (S.additionalRetainedSystem T))
        (QuantumChannel.comp
          (QuantumChannel.unitaryConj (S.additionalRetainedFactorSwap T))
          (QuantumChannel.unitaryConj (S.complementFactorization T hST))) :=
  rfl
end QEC.Semantics.QuditSubsystem
