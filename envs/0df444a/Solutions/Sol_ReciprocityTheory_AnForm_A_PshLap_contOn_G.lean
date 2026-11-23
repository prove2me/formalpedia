-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PshLap.contOn_G
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:16:20.756847+00:00
-- url     : https://prove2.me/submissions/4397ae77-1aef-4bdd-90f3-a13e26071070

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
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PshLap
noncomputable section
variable {V : Set ℂ} {g : ℂ → ℝ} {G : ℂ → ℂ →L[ℝ] ℝ} {H : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ}
namespace ReciprocityTheory.AnForm.A.PshLap
theorem _root_.solution (hGc : ContinuousOn G V) {R a : ℝ} (hR : closedBall (0:ℂ) R ⊆ V) :
    ContinuousOn (Function.uncurry fun r θ => G (circleMap 0 r θ) (circleMap 0 1 θ))
      (Icc 0 R ×ˢ Icc 0 a) :=
  (hGc.comp continuous_circleMap_uncurry.continuousOn (mapsTo_rect hR)).clm_apply
    ((continuous_circleMap 0 1).comp continuous_snd).continuousOn
end ReciprocityTheory.AnForm.A.PshLap
