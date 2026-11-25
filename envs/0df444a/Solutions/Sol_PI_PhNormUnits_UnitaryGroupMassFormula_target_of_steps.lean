-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.target_of_steps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:10:23.60417+00:00
-- url     : https://prove2.me/submissions/0f05b110-cff6-4912-a7d3-fd8a772ea0da

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_Development
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_target_of_hyp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open PI PI.PhNormUnits PI.PhNormUnits.UnitaryGroupMassFormula
open PI.PhNormUnits
namespace PI.PhNormUnits.UnitaryGroupMassFormula
theorem _root_.solution (hU : StepUnits) (hA : StepAll) (hT : StepTrace) (hS : StepSum) : Target := by
  refine target_of_hyp ?_
  intro p _ l ex ph S hH
  have hsw : ∀ α ∈ S, SwapRel p l ex ph α := hA p l ex ph S hH (hU p l ex ph S hH)
  exact hS p l ex ph S hH hsw (hT p l ex ph S hH hsw)
end PI.PhNormUnits.UnitaryGroupMassFormula
