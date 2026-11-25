-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_pointFormRank_holds_eq_zero_of_eventually_eval_602689fad780
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:59:12.649438+00:00
-- url     : https://prove2.me/submissions/807609db-b511-459a-bc10-fd51724ab2ae

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExMapAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StRatioAlgDep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_EqZeroOfEventuallyEval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights.Inter
namespace pointFormRank_holds
theorem _root_.solution {d : ℕ} (f : MvPolynomial (Fin d) ℂ) (a : Fin d → ℂ)
    (h : ∀ᶠ z in 𝓝 a, eval z f = 0) : f = 0 := by
  have han : AnalyticOnNhd ℂ (fun z => eval z f) Set.univ := AnalyticOnNhd.eval_mvPolynomial f
  have h0 := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ a) h
  exact MvPolynomial.funext fun z => by simpa using h0 (Set.mem_univ z)
end pointFormRank_holds
end GroundTheory.Heights₂.Heights.Inter
