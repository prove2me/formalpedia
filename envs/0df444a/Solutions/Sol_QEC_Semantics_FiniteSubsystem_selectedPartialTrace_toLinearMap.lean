-- Prove2me | solution 1 for QEC.Semantics.FiniteSubsystem.selectedPartialTrace_toLinearMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:08:28.927345+00:00
-- url     : https://prove2.me/submissions/f91bba3f-342d-43be-b6ce-4ee12aea5913

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
theorem _root_.solution (S : FiniteSubsystem ι) :
    S.selectedPartialTrace.toLinearMap =
      partialTraceRightRaw S.selectedSystem S.complementSystem :=
  rfl
end QEC.Semantics.FiniteSubsystem
