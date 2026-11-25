-- Prove2me | solution 1 for PI.WhitFunctDualWork.besselEdge_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:14:50.37381+00:00
-- url     : https://prove2.me/submissions/5932bf82-7941-4d65-bd37-be296d4263ff

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WhitFunctDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WhittakerFunctionalDual_StableOfIrreducible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.WhitFunctDualWork
open Formalism.L2.SG.GGMirabolic
namespace PI.WhitFunctDualWork
theorem _root_.solution (i j : ℕ) : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselEdge 0 0 i j ↔ j = i + 1 := by
  unfold Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselEdge
  constructor <;> intro h <;> omega
end PI.WhitFunctDualWork
