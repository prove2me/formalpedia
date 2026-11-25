-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PolydiscLelongLimit_hypIncl_mem_ball_c348fbc1b221
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:47:22.319469+00:00
-- url     : https://prove2.me/submissions/873ce181-55da-4ca9-9cf1-a3eb06849a94

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolydiscLelongLimit
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ProjectiveLineZeroFormHolds
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPolydiscLelongLimit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.PolydiscLelongLimit
namespace GroundTheory.Heights₂.Heights.PolydiscLelongLimit
theorem _root_.solution {d : ℕ} {r : ℝ} (w : Fin d → ℂ) :
    hypIncl w ∈ Metric.ball (0 : Fin (d + 1) → ℂ) r ↔ w ∈ Metric.ball 0 r := by
  rcases le_or_gt r 0 with hr | hr
  · simp [Metric.ball_eq_empty.2 hr]
  · simp only [mem_ball_zero_iff, pi_norm_lt_iff hr, Fin.forall_fin_succ, hypIncl, Fin.cons_zero,
      Fin.cons_succ, norm_zero, hr, true_and]
end GroundTheory.Heights₂.Heights.PolydiscLelongLimit
