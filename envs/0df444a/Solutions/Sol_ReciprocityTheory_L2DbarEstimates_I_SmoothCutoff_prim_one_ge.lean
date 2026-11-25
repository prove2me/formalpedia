-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.SmoothCutoff.prim_one_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:40:18.711979+00:00
-- url     : https://prove2.me/submissions/96eca5ec-1f39-46ac-a2e1-d89bd2c175c2

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_Cutoff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_SmoothCutoff_bump_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_SmoothCutoff_bump_nonneg
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_SmoothCutoff_bump_of_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
open ReciprocityTheory.L2DbarEstimates.I.SmoothCutoff
namespace ReciprocityTheory.L2DbarEstimates.I.SmoothCutoff
theorem _root_.solution : 2 / 5 ≤ prim 1 := by
  unfold prim
  have hi : ∀ a b : ℝ, IntervalIntegrable bump volume a b :=
    fun a b => bump_continuous.intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 19 / 20) (hi _ _) (hi _ _),
    ← intervalIntegral.integral_add_adjacent_intervals (a := 0) (b := 11 / 20) (hi _ _) (hi _ _)]
  have h1 : 0 ≤ ∫ s in (0 : ℝ)..11 / 20, bump s :=
    intervalIntegral.integral_nonneg (by norm_num) (fun s _ => bump_nonneg s)
  have h3 : 0 ≤ ∫ s in (19 / 20 : ℝ)..1, bump s :=
    intervalIntegral.integral_nonneg (by norm_num) (fun s _ => bump_nonneg s)
  have h2 : ∫ s in (11 / 20 : ℝ)..19 / 20, bump s = 2 / 5 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ))]
    · simp; norm_num
    · intro s hs
      rw [Set.uIcc_of_le (by norm_num)] at hs
      exact bump_of_mem hs.1 hs.2
  linarith
end ReciprocityTheory.L2DbarEstimates.I.SmoothCutoff
