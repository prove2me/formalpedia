-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PshLap.contOn_H
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:05:02.245849+00:00
-- url     : https://prove2.me/submissions/9704f598-8fec-4bcc-a1e0-0271464c7f63

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshLap
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_continuous_circleMap_uncurry
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_mapsTo_rect

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
open MeasureTheory Metric Set Filter Topology Real
open MeasureTheory Metric Set Filter Topology Real
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PshLap
noncomputable section
variable {V : Set ℂ} {g : ℂ → ℝ} {G : ℂ → ℂ →L[ℝ] ℝ} {H : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ}
namespace ReciprocityTheory.AnForm.A.PshLap
theorem _root_.solution (hHc : ContinuousOn H V) {R a : ℝ} (hR : closedBall (0:ℂ) R ⊆ V) :
    ContinuousOn (Function.uncurry fun s θ =>
      H (circleMap 0 s θ) (circleMap 0 1 θ) (circleMap 0 1 θ) +
        H (circleMap 0 s θ) (circleMap 0 1 θ * Complex.I) (circleMap 0 1 θ * Complex.I))
      (Icc 0 R ×ˢ Icc 0 a) := by
  have hc := hHc.comp continuous_circleMap_uncurry.continuousOn (mapsTo_rect (a := a) hR)
  have he : Continuous fun p : ℝ × ℝ => circleMap 0 1 p.2 :=
    (continuous_circleMap 0 1).comp continuous_snd
  refine ContinuousOn.add ((hc.clm_apply he.continuousOn).clm_apply he.continuousOn) ?_
  exact (hc.clm_apply (he.mul continuous_const).continuousOn).clm_apply
    (he.mul continuous_const).continuousOn
end ReciprocityTheory.AnForm.A.PshLap
