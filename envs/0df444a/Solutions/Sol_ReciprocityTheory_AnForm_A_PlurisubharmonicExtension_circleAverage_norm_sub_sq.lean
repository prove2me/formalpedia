-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.circleAverage_norm_sub_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:03:34.385053+00:00
-- url     : https://prove2.me/submissions/6ced32a3-dbf5-497a-980c-af1f9f07b408

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshPoisson
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtA
import Theorems.Thm_ReciprocityTheory_AnForm_A_PlurisubharmonicExtension_cA_mul

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
theorem _root_.solution (a c : ℂ) {s : ℝ} (hs : 0 ≤ s) :
    circleAverage (fun ζ => ‖ζ - c‖ ^ 2) a s = ‖a - c‖ ^ 2 + s ^ 2 := by
  have hpt : ∀ ζ ∈ sphere a |s|, ‖ζ - c‖ ^ 2 =
      (‖a - c‖ ^ 2 + s ^ 2) + 2 * ((starRingEnd ℂ (a - c)) * (ζ - a)).re := by
    intro ζ hζ
    rw [abs_of_nonneg hs, mem_sphere, dist_eq_norm] at hζ
    have : ζ - c = (a - c) + (ζ - a) := by ring
    rw [this, ← hζ, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_add]
    simp [Complex.mul_re]
    ring
  rw [circleAverage_congr_sphere hpt]
  have hh : circleAverage (fun ζ => (starRingEnd ℂ (a - c)) * (ζ - a)) a s = 0 := by
    rw [circleAverage_of_differentiable_on_off_countable (s := ∅) Set.countable_empty]
    · simp
    · exact (by fun_prop : Continuous fun ζ : ℂ => (starRingEnd ℂ (a - c)) * (ζ - a)).continuousOn
    · intro z _; fun_prop
  have hre : circleAverage (fun ζ => ((starRingEnd ℂ (a - c)) * (ζ - a)).re) a s = 0 := by
    have h2 : CircleIntegrable (fun ζ => (starRingEnd ℂ (a - c)) * (ζ - a)) a s :=
      (by fun_prop : Continuous fun ζ : ℂ => (starRingEnd ℂ (a - c)) * (ζ - a)).continuousOn.circleIntegrable'
    have := Complex.reCLM.circleAverage_comp_comm h2
    simp only [Function.comp_def, Complex.reCLM_apply] at this
    rw [this, hh]; simp
  have h2 : circleAverage (fun x => 2 * ((starRingEnd ℂ) (a - c) * (x - a)).re) a s =
      2 * circleAverage (fun x => ((starRingEnd ℂ) (a - c) * (x - a)).re) a s :=
    cA_mul _ _ _ _
  rw [circleAverage_fun_add, circleAverage_const, h2, hre]
  · simp
  · exact (continuous_const).continuousOn.circleIntegrable'
  · exact (by fun_prop : Continuous fun ζ : ℂ => 2 * ((starRingEnd ℂ (a - c)) * (ζ - a)).re).continuousOn.circleIntegrable'
end ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
