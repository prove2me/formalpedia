-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PshLap.circleMap_mem_closedBall
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:54:46.418858+00:00
-- url     : https://prove2.me/submissions/24fd3526-f6f0-45d7-9049-0cde26fd2017

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshLap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PshLap
noncomputable section
variable {V : Set ℂ} {g : ℂ → ℝ} {G : ℂ → ℂ →L[ℝ] ℝ} {H : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ}
namespace ReciprocityTheory.AnForm.A.PshLap
theorem _root_.solution {r R θ : ℝ} (h0 : 0 ≤ r) (h : r ≤ R) :
    circleMap 0 r θ ∈ closedBall (0:ℂ) R := by
  simp [abs_of_nonneg h0, h]
end ReciprocityTheory.AnForm.A.PshLap
