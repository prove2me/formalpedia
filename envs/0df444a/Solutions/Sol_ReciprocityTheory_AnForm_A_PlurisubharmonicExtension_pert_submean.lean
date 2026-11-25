-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.pert_submean
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:11:43.112839+00:00
-- url     : https://prove2.me/submissions/778d85d7-11ff-4743-b062-62cfea6f63ac

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshPoisson
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtA
import Theorems.Thm_ReciprocityTheory_AnForm_A_PlurisubharmonicExtension_cA_mul
import Theorems.Thm_ReciprocityTheory_AnForm_A_PlurisubharmonicExtension_circleAverage_norm_sub_sq

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
theorem _root_.solution {E : Finset ℂ} {c a : ℂ} {s ε δ : ℝ} (hs : 0 < s) (hε : 0 ≤ ε)
    (haE : a ∉ E) (hE : ∀ f ∈ E, f ∉ sphere a s) :
    CircleIntegrable (pert E c ε δ) a s ∧
      pert E c ε δ a + δ * s ^ 2 ≤ circleAverage (pert E c ε δ) a s := by
  have hlogc : ∀ f ∈ E, ContinuousOn (fun ζ : ℂ => log ‖ζ - f‖) (sphere a |s|) := by
    intro f hf
    apply ContinuousOn.log (by fun_prop)
    intro x hx hx0
    rw [norm_eq_zero, sub_eq_zero] at hx0
    rw [abs_of_pos hs] at hx
    exact hE f hf (hx0 ▸ hx)
  have hli : ∀ f ∈ E, CircleIntegrable (fun ζ : ℂ => log ‖ζ - f‖) a s :=
    fun f hf => (hlogc f hf).circleIntegrable'
  have hsumc : ContinuousOn (fun ζ : ℂ => ∑ f ∈ E, log ‖ζ - f‖) (sphere a |s|) :=
    continuousOn_finsetSum E hlogc
  have hqi : CircleIntegrable (fun ζ : ℂ => δ * ‖ζ - c‖ ^ 2) a s :=
    (by fun_prop : Continuous fun ζ : ℂ => δ * ‖ζ - c‖ ^ 2).continuousOn.circleIntegrable'
  have hsi : CircleIntegrable (fun ζ : ℂ => ε * ∑ f ∈ E, log ‖ζ - f‖) a s :=
    (continuousOn_const.mul hsumc).circleIntegrable'
  refine ⟨hsi.add hqi, ?_⟩
  unfold pert
  rw [circleAverage_fun_add hsi hqi]
  have h1 : circleAverage (fun ζ : ℂ => ε * ∑ f ∈ E, log ‖ζ - f‖) a s
      = ε * ∑ f ∈ E, circleAverage (fun ζ : ℂ => log ‖ζ - f‖) a s := by
    rw [show circleAverage (fun ζ : ℂ => ε * ∑ f ∈ E, log ‖ζ - f‖) a s
      = ε * circleAverage (fun ζ : ℂ => ∑ f ∈ E, log ‖ζ - f‖) a s from cA_mul _ _ _ _]
    rw [circleAverage_fun_sum hli]
  have h2 : circleAverage (fun ζ : ℂ => δ * ‖ζ - c‖ ^ 2) a s = δ * (‖a - c‖ ^ 2 + s ^ 2) := by
    rw [show circleAverage (fun ζ : ℂ => δ * ‖ζ - c‖ ^ 2) a s
      = δ * circleAverage (fun ζ : ℂ => ‖ζ - c‖ ^ 2) a s from cA_mul _ _ _ _]
    rw [circleAverage_norm_sub_sq a c hs.le]
  rw [h1, h2]
  have h3 : ∑ f ∈ E, log ‖a - f‖ ≤ ∑ f ∈ E, circleAverage (fun ζ : ℂ => log ‖ζ - f‖) a s := by
    apply Finset.sum_le_sum
    intro f hf
    have haf : a - f ≠ 0 := sub_ne_zero.2 (fun h => haE (h ▸ hf))
    rw [circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hs.ne']
    have : log ‖a - f‖ = log s + log (s⁻¹ * ‖a - f‖) := by
      rw [log_mul (inv_ne_zero hs.ne') (norm_ne_zero_iff.2 haf), log_inv]; ring
    rw [this]
    have : log (s⁻¹ * ‖a - f‖) ≤ log⁺ (s⁻¹ * ‖a - f‖) := le_max_right _ _
    linarith
  have h4 := mul_le_mul_of_nonneg_left h3 hε
  nlinarith
end ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
