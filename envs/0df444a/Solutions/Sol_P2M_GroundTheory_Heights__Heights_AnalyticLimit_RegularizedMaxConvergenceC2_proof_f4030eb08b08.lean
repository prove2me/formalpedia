-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AnalyticLimit_RegularizedMaxConvergenceC2_proof_f4030eb08b08
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:59:41.466392+00:00
-- url     : https://prove2.me/submissions/4109e9f5-d32b-4d92-b46b-b6c50773b559

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_RegularizedMaxC2ExampleRealLine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_dist_lt_iff_norm_sub_73d8e6366e39
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_norm_fderiv2_regMax_le_7137d271ab9b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_norm_le_sum_norm_6cec29ee2c33
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_abs_le_sum_abs_2d73530beb3a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_regMax_c2_pointwise_bound_0941e6435e3b
import Theorems.Thm_ReciprocityTheory_AnForm_A_abs_regMax_le
import Theorems.Thm_ReciprocityTheory_AnForm_A_fderiv2_regMax
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_add_const
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_comp_fderiv2
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_contDiff
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_fderiv_nonneg
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_fderiv_sum
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_one_fderiv2_bound
import Theorems.Thm_ReciprocityTheory_AnForm_A_two_le_inf
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open Filter Topology Metric
open ReciprocityTheory.AnForm.A (regMax regMax_contDiff regMax_add_const abs_regMax_le regMax_fderiv_sum
  regMax_fderiv_nonneg fderiv2_regMax regMax_one_fderiv2_bound regMax_comp_fderiv2 two_le_inf)
noncomputable section
namespace GroundTheory.Heights₂.Heights.AnalyticLimit
namespace RegularizedMaxConvergenceC2
theorem _root_.solution : RegularizedMaxConvergenceC2.Statement := by
  intro E _ _ ι _ _ U K f u ε δ hU hK hf hev hε hc hδ hδε
  obtain ⟨C, hC⟩ := norm_fderiv2_regMax_le (ι := ι)
  have hC0 : 0 ≤ C := by
    simpa using (hC 1 one_pos 0).trans' (norm_nonneg (fderiv ℝ (fderiv ℝ (regMax (ι := ι) 1)) 0))
  have hc0 : ∀ j, ∀ e > 0, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ x ∈ K, |u t j x - f x| < e := fun j e he =>
    (Metric.tendstoUniformlyOn_iff.1 (hc j).1 e he).mono fun t ht x hx => by
      simpa [Real.dist_eq, abs_sub_comm] using ht x hx
  have hc1 : ∀ j, ∀ e > 0, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ x ∈ K,
      ‖fderiv ℝ (u t j) x - fderiv ℝ f x‖ < e := fun j e he =>
    (Metric.tendstoUniformlyOn_iff.1 (hc j).2.1 e he).mono fun t ht x hx => by
      simpa [dist_eq_norm, norm_sub_rev] using ht x hx
  have hc2 : ∀ j, ∀ e > 0, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ x ∈ K,
      ‖fderiv ℝ (fderiv ℝ (u t j)) x - fderiv ℝ (fderiv ℝ f) x‖ < e := fun j e he =>
    ((Metric.tendstoUniformlyOn_iff (α := E →L[ℝ] E →L[ℝ] ℝ)).1 (hc j).2.2 e he).mono
      fun t ht x hx => (dist_lt_iff_norm_sub (F := E →L[ℝ] E →L[ℝ] ℝ)).1 (ht x hx)
  refine ⟨Metric.tendstoUniformlyOn_iff.2 fun e he => ?_,
    Metric.tendstoUniformlyOn_iff.2 fun e he => ?_,
    (Metric.tendstoUniformlyOn_iff (α := E →L[ℝ] E →L[ℝ] ℝ)).2 fun e he => ?_⟩
  · filter_upwards [hev, eventually_all.2 fun j => hc0 j (e / 3) (by positivity),
      hε.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < e / 3))] with t ht h0 hεe
    intro x hx
    have P := regMax_c2_pointwise_bound hU hf ht.2 ht.1 (hC _ ht.1) (hK hx)
      (fun j => (h0 j x hx).le) (fun j => norm_le_sum_norm (fun i => fderiv ℝ (u t i) x - fderiv ℝ f x) j)
      (fun j => norm_le_sum_norm
        (fun i => fderiv ℝ (fderiv ℝ (u t i)) x - fderiv ℝ (fderiv ℝ f) x) j)
    rw [Real.dist_eq, abs_sub_comm]
    linarith [P.1]
  · filter_upwards [hev, eventually_all.2 fun j => hc1 j (e / 2) (by positivity)] with t ht h1
    intro x hx
    have P := regMax_c2_pointwise_bound hU hf ht.2 ht.1 (hC _ ht.1) (hK hx)
      (fun j => abs_le_sum_abs (fun i => u t i x - f x) j) (fun j => (h1 j x hx).le)
      (fun j => norm_le_sum_norm
        (fun i => fderiv ℝ (fderiv ℝ (u t i)) x - fderiv ℝ (fderiv ℝ f) x) j)
    rw [dist_eq_norm, norm_sub_rev]
    linarith [P.2.1]
  · filter_upwards [hev, hδ, eventually_all.2 fun j => hc2 j (e / 8) (by positivity),
      hδε.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < e / (8 * (C + 1))))]
      with t ht hδt h2 hr
    intro x hx
    have P := regMax_c2_pointwise_bound hU hf ht.2 ht.1 (hC _ ht.1) (hK hx)
      (fun j => abs_le_sum_abs (fun i => u t i x - f x) j) (fun j => hδt j x hx)
      (fun j => (h2 j x hx).le)
    refine (dist_lt_iff_norm_sub (F := E →L[ℝ] E →L[ℝ] ℝ)).2 ?_
    have hq0 : 0 ≤ δ t ^ 2 / ε t := div_nonneg (sq_nonneg _) ht.1.le
    have hq : C * (δ t ^ 2 / ε t) < e / 8 := by
      calc C * (δ t ^ 2 / ε t) ≤ (C + 1) * (δ t ^ 2 / ε t) := by nlinarith
        _ < (C + 1) * (e / (8 * (C + 1))) := mul_lt_mul_of_pos_left hr (by linarith)
        _ = e / 8 := by field_simp
    have e1 : C / ε t * δ t ^ 2 = C * (δ t ^ 2 / ε t) := by ring
    have := P.2.2
    rw [e1] at this
    linarith
end RegularizedMaxConvergenceC2
end GroundTheory.Heights₂.Heights.AnalyticLimit
