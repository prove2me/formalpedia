-- Prove2me | solution 1 for PI.AmpRootCommon.Tri.measurable_extNe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:19:03.709853+00:00
-- url     : https://prove2.me/submissions/b464b4de-e82f-4c2a-ae41-8774d95ec629

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupBasics_TriDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupBasics_TriShear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
noncomputable section
open PI PI.AmpRootCommon PI.AmpRootCommon.Tri
namespace PI.AmpRootCommon.Tri
theorem _root_.solution {ι : Type} [DecidableEq ι] (a : ι) : Measurable (extNe a) := by
  refine measurable_pi_lambda _ (fun j => ?_)
  by_cases h : j ≠ a
  · simp only [extNe, dif_pos h]
    exact measurable_pi_apply _
  · simp only [extNe, dif_neg h]
    exact measurable_const
end PI.AmpRootCommon.Tri
