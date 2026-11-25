-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_cons_mem_ball_one_42c41052423a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:49:28.144809+00:00
-- url     : https://prove2.me/submissions/2bf997b0-b4ec-460d-b1c1-29a57e6a1800

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StRiemannSlices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PRiemannExtensionSlices
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_mem_ball_pi_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Complex Metric MeasureTheory Set Filter Topology ReciprocityTheory.AnForm.Osgood
open scoped Real
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.RiemannExtensionSlices
namespace GroundTheory.Heights₂.Heights.Regular.RiemannExtensionSlices
theorem _root_.solution {n : ℕ} {x : ℂ} (hx : ‖x‖ < 1) {y : Fin n → ℂ}
    (hy : y ∈ ball (0 : Fin n → ℂ) 1) : (Fin.cons x y : Fin (n + 1) → ℂ) ∈ ball 0 1 := by
  refine (mem_ball_pi_iff one_pos).mpr fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hx
  · simpa using (mem_ball_pi_iff one_pos).mp hy j
end GroundTheory.Heights₂.Heights.Regular.RiemannExtensionSlices
