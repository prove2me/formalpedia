-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_CurveVertPointLength_proof_d843ff5f15ea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:09:24.290739+00:00
-- url     : https://prove2.me/submissions/60ff3e15-2329-4e69-9d99-48345f818671

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveVertPointLengthSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_CurveCountObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_MultAtPosOfMemDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveVertPointLength
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointLength_maximal_and_mult_eq_94228b17e362
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_multAt_pos_of_mem_divSupp_5458a53f671d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
namespace GroundTheory.Heights₂.Heights.Targets
namespace CurveVertPointLength
theorem _root_.solution (hCh : CurveVertPointChart.Statement) (hInj : CurveVertPointInj.Statement)
    (hSurj : CurveVertPointSurj.Statement) (hMC : CurveVertPointMultChart.Statement)
    (hSQ : CurveSectionQuotLocal.Statement) : CurveVertPointLength.Statement := by
  intro K _ ι _ Ω _ y s d hP hs hsP
  refine ⟨⟨fun W hW => ?_, hInj K ι Ω y s d hP hs hsP,
      fun m hm => hSurj K ι Ω y s d hP hs hsP m hm.1 hm.2⟩,
    fun W hW => (CurveVerticalPointLength.maximal_and_mult_eq hCh hMC hSQ hP hs hsP hW).2⟩
  obtain ⟨hmax, hmult⟩ := CurveVerticalPointLength.maximal_and_mult_eq hCh hMC hSQ hP hs hsP hW
  exact ⟨hmax, hmult ▸ (IndefiniteRowSideFullHecke.Inter.multAt_pos_of_mem_divSupp hW).ne'⟩
end CurveVertPointLength
end GroundTheory.Heights₂.Heights.Targets
