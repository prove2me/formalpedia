-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PshLap.mapsTo_rect
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:00:46.78574+00:00
-- url     : https://prove2.me/submissions/7c70f128-d79c-4b0c-8641-dc223e144a77

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshLap
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_circleMap_mem_closedBall

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
theorem _root_.solution {R a : ℝ} (hR : closedBall (0:ℂ) R ⊆ V) :
    MapsTo (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) (Icc 0 R ×ˢ Icc 0 a) V :=
  fun _ hp => hR (circleMap_mem_closedBall hp.1.1 hp.1.2)
end ReciprocityTheory.AnForm.A.PshLap
