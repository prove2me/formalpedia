-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.smg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:37:44.978792+00:00
-- url     : https://prove2.me/submissions/0727116f-c332-41c3-9ae1-bce41f61983f

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshPoisson
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtA
import Theorems.Thm_ReciprocityTheory_AnForm_A_PlurisubharmonicExtension_smg2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Real Filter Topology MeasureTheory
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
namespace ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
theorem _root_.solution {g : ℂ → ℝ} {r : ℝ} {F : Finset ℂ} (hr : 0 < r) (hF0 : (0 : ℂ) ∉ F)
    (hFr : ∀ f ∈ F, f ∈ ball (0 : ℂ) r)
    (hc : ContinuousOn g (closedBall 0 r \ ↑F))
    (hB : ∃ B, ∀ ζ ∈ closedBall (0 : ℂ) r \ ↑F, g ζ ≤ B)
    (hsub : ∀ a s, 0 < s → closedBall a s ⊆ ball (0 : ℂ) r \ ↑F → g a ≤ circleAverage g a s) :
    g 0 ≤ circleAverage g 0 r := by
  obtain ⟨B, hB⟩ := hB
  refine smg2 hr hF0 hFr hc ?_ hsub
  intro ε hε T
  refine ⟨exp ((T - B) / ε), exp_pos _, ?_⟩
  intro e he ζ hζ hd
  have hne : ζ - e ≠ 0 := sub_ne_zero.2 (fun h => hζ.2 (h ▸ he))
  have hlog : log ‖ζ - e‖ < (T - B) / ε := by
    rw [dist_eq_norm] at hd
    exact (log_lt_iff_lt_exp (norm_pos_iff.2 hne)).2 hd
  have : ε * log ‖ζ - e‖ < T - B := by
    have := mul_lt_mul_of_pos_left hlog hε
    rwa [mul_div_cancel₀ _ hε.ne'] at this
  linarith [hB ζ hζ]
end ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
