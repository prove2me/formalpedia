-- Prove2me | solution 1 for PI.UG.W.unimodGenus_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:32:41.922836+00:00
-- url     : https://prove2.me/submissions/90f4612a-0c28-48ef-a77a-38e097dc9c6e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnimodGenus
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularGenus_Development

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open PI PI.UG PI.UG.W
namespace PI.UG.W
theorem _root_.solution (h1 : UnimodLocal) (h2 : IsomLocStd) : PI.UnimodGenus := by
  intro E _ _ _ n hE N hN hU p hp
  exact h2 E n hE N hN p hp (h1 E n N hN hU p hp)
end PI.UG.W
