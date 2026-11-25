-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_RegChartData_near_point_f569195abf0f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:33:48.833409+00:00
-- url     : https://prove2.me/submissions/aef059fc-7207-43cb-bdee-96138c12b846

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StatementsTruncPsh
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_GlueCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PChartComparison
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PMollifiedNearSmooth
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_PotentialCharts_mid_subset_source_96b409876f03
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_polyMax_le__638c0d78514a
import Theorems.Thm_ReciprocityTheory_AnForm_A_mollify_thm


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
open Metric
open scoped ContDiff
open ReciprocityTheory.AnForm.A (polyMax molli mollify_thm polyMax_le' coordDiv limsupExt)
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.RegChartData
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : ReciprocityTheory.AnForm.M.FinHolAtlas D X}
  (R : RegChartData A)
namespace GroundTheory.Heights₂.Heights.Regular.RegChartData
theorem _root_.solution {t B : ℝ} (ht : 0 < t) (hB : ∀ j, ∀ y ∈ (R.chart j).target, |R.f j y| ≤ B)
    (htB : t ≤ Real.exp (-B) / 4) {j : Fin R.N} {x : X} (hx : x ∈ R.mid j) (hxY : x ∈ R.Yo)
    (hr : R.r x ≤ Real.log t⁻¹) {y : Fin D → ℂ} (hy : y ∈ closedBall (R.chart j x) t)
    (hyT : y ∈ (R.chart j).target) :
    y ∉ coordDiv (R.S j) ∧
      R.r ((R.chart j).symm y) ≤ Real.log t⁻¹ + (2 * B + D * Real.log 4) := by
  have hxs : x ∈ (R.chart j).source := R.mid_subset_source j hx
  obtain ⟨z, hz⟩ : ∃ z, z = R.chart j x := ⟨_, rfl⟩
  rw [← hz] at hy
  have hzT : z ∈ (R.chart j).target := hz ▸ (R.chart j).map_source hxs
  have hzA : z ∉ coordDiv (R.S j) := hz ▸ (R.mem_Yo j x hxs).1 hxY
  have hzx : (R.chart j).symm z = x := hz ▸ (R.chart j).left_inv hxs
  have hrx : R.r x = Real.exp 1 + R.f j z + ∑ i ∈ R.S j, Real.log (‖z i‖ ^ 2)⁻¹ := by
    have := R.r_chart j z ⟨hzT, hzA⟩
    rwa [hzx] at this
  have hnn : ∀ w ∈ (R.chart j).target, ∀ i, 0 ≤ Real.log (‖w i‖ ^ 2)⁻¹ := by
    intro w hw i
    have hw1 : ‖w‖ < 1 := by simpa using R.target_subset j hw
    rw [Real.log_inv]
    exact neg_nonneg.2 (Real.log_nonpos (by positivity)
      (pow_le_one₀ (norm_nonneg _) ((norm_le_pi_norm w i).trans hw1.le)))
  have hsum : ∑ i ∈ R.S j, Real.log (‖z i‖ ^ 2)⁻¹ ≤ Real.log t⁻¹ + B := by
    have h1 := hB j z hzT
    have h2 := neg_abs_le (R.f j z)
    have h3 := Real.exp_pos 1
    linarith
  have hzi : ∀ i ∈ R.S j, 2 * t ≤ ‖z i‖ := by
    intro i hi
    have hpos : 0 < ‖z i‖ := norm_pos_iff.2 fun h0 => hzA ⟨i, hi, h0⟩
    have hle : Real.log (‖z i‖ ^ 2)⁻¹ ≤ Real.log t⁻¹ + B :=
      (Finset.single_le_sum (f := fun i => Real.log (‖z i‖ ^ 2)⁻¹) (fun i _ => hnn z hzT i) hi).trans
        hsum
    by_contra hlt'
    have hlt := not_le.1 hlt'
    have hE := Real.exp_pos (-B)
    have h4 : 4 * t * t ≤ t * Real.exp (-B) := by nlinarith
    have ha : ‖z i‖ ^ 2 < t * Real.exp (-B) := by nlinarith
    have hlog : Real.log t⁻¹ + B < Real.log (‖z i‖ ^ 2)⁻¹ := by
      have h1 : Real.log (t * Real.exp (-B))⁻¹ = Real.log t⁻¹ + B := by
        rw [Real.log_inv, Real.log_mul ht.ne' hE.ne', Real.log_exp, Real.log_inv]; ring
      rw [← h1]
      exact Real.log_lt_log (by positivity) ((inv_lt_inv₀ (by positivity) (by positivity)).2 ha)
    linarith
  have hyz : ∀ i, ‖z i‖ ≤ ‖y i‖ + t := by
    intro i
    have h1 : ‖y i - z i‖ ≤ t :=
      (norm_le_pi_norm (y - z) i).trans (by rw [← dist_eq_norm]; exact mem_closedBall.1 hy)
    have h2 := norm_sub_norm_le (z i) (y i)
    rw [norm_sub_rev] at h2
    linarith
  have hyi : ∀ i ∈ R.S j, ‖z i‖ / 2 ≤ ‖y i‖ := fun i hi => by linarith [hzi i hi, hyz i]
  have hyA : y ∉ coordDiv (R.S j) := by
    rintro ⟨i, hi, h0⟩
    have h3 : ‖y i‖ = 0 := by rw [h0, norm_zero]
    linarith [hyi i hi, hzi i hi]
  refine ⟨hyA, ?_⟩
  have hterm : ∀ i ∈ R.S j,
      Real.log (‖y i‖ ^ 2)⁻¹ ≤ Real.log (‖z i‖ ^ 2)⁻¹ + Real.log 4 := by
    intro i hi
    have hzp : 0 < ‖z i‖ := by linarith [hzi i hi]
    have hyp : 0 < ‖y i‖ := by linarith [hyi i hi]
    rw [Real.log_inv, Real.log_inv]
    have : Real.log (‖z i‖ ^ 2) - Real.log 4 ≤ Real.log (‖y i‖ ^ 2) := by
      rw [← Real.log_div (by positivity) (by norm_num)]
      exact Real.log_le_log (by positivity) (by nlinarith [hyi i hi])
    linarith
  have hS : ∑ i ∈ R.S j, Real.log (‖y i‖ ^ 2)⁻¹ ≤
      ∑ i ∈ R.S j, Real.log (‖z i‖ ^ 2)⁻¹ + D * Real.log 4 := by
    have h1 := Finset.sum_le_sum hterm
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at h1
    have h2 : ((R.S j).card : ℝ) ≤ D := by
      have := Finset.card_le_univ (R.S j)
      rw [Fintype.card_fin] at this
      exact_mod_cast this
    have h3 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    nlinarith
  rw [R.r_chart j y ⟨hyT, hyA⟩]
  have h1 := hB j y hyT
  have h2 := le_abs_self (R.f j y)
  have h3 := hB j z hzT
  have h4 := neg_abs_le (R.f j z)
  linarith
end GroundTheory.Heights₂.Heights.Regular.RegChartData
