-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_PolyMaxLowerBound_proof_6d4135254189
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:08:48.000693+00:00
-- url     : https://prove2.me/submissions/648a856f-e9b7-4f8e-93ea-22162a2feab5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PPolyMaxLowerBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_PolyMaxLowerBound_exists_pos_le_cb4257d68214
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_PolyMaxLowerBound_chart_margin_fee00aa2a23d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_PolyMaxLowerBound_exists_far_point_77b620157daf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_PolyMaxLowerBound_log_inv_half_sq_80bf2af2ba69

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
open Metric Set
open ReciprocityTheory.AnForm.A (polyMax coordDiv limsupExt)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
namespace PolyMaxLowerBound
theorem _root_.solution : PolyMaxLowerBound.Statement := by
  intro X _ _ _ D A R
  obtain ⟨B, hB⟩ := R.f_bdd
  choose δf Qf hδf hQf hball using PolyMaxLowerBound.chart_margin R
  obtain ⟨δ, hδ0, hδle⟩ := PolyMaxLowerBound.exists_pos_le δf hδf
  set Q : ℝ := ∑ j, Qf j with hQdef
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun j _ => hQf j
  have hQj : ∀ j, Qf j ≤ Q := fun j =>
    Finset.single_le_sum (f := Qf) (fun k _ => hQf k) (Finset.mem_univ j)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  set Λ : ℝ := Real.exp 1 + |B| + 2 * D * Real.log 2 + 2 * D with hΛdef
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have hΛ1 : 1 ≤ Λ := by
    have : 0 ≤ 2 * (D : ℝ) * Real.log 2 := by positivity
    have : 0 ≤ |B| := abs_nonneg B
    linarith
  have hlogΛ : 0 ≤ Real.log Λ := Real.log_nonneg hΛ1
  set C : ℝ := Q + |R.Clog| * (Real.log Λ + 1) with hCdef
  have hC0 : 0 ≤ C := by positivity
  refine ⟨C, min δ (Real.exp (-Real.exp 1)), lt_min hδ0 (Real.exp_pos _), ?_⟩
  intro t ht htt K j x hx
  have htδ : t ≤ δ := (htt.trans_le (min_le_left _ _)).le
  have hte : t < Real.exp (-Real.exp 1) := htt.trans_le (min_le_right _ _)
  set ℓ : ℝ := Real.log t⁻¹ with hℓdef
  have hℓe : Real.exp 1 < ℓ := by
    rw [hℓdef, Real.lt_log_iff_exp_lt (inv_pos.2 ht)]
    rw [Real.exp_neg] at hte
    exact (lt_inv_comm₀ ht (Real.exp_pos _)).1 hte
  have hℓ1 : 1 ≤ ℓ := he1.trans hℓe.le
  have hlogℓ : 1 ≤ Real.log ℓ := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hℓe.le
  obtain ⟨y, hy, hyn⟩ := PolyMaxLowerBound.exists_far_point (R.chart j x) ht
  obtain ⟨hyT, hqy⟩ := hball j x hx y (closedBall_subset_closedBall (htδ.trans (hδle j)) hy)
  have hyD : y ∉ coordDiv (R.S j) := by
    rintro ⟨i, -, hi⟩
    have := hyn i
    rw [hi, norm_zero] at this
    linarith
  have hsrc := (R.chart j).map_target hyT
  have hYo : (R.chart j).symm y ∈ R.Yo :=
    (R.mem_Yo j _ hsrc).2 (by rwa [(R.chart j).right_inv hyT])
  have hr1 := R.one_le_r _ hYo

  have hsum : ∑ i ∈ R.S j, Real.log (‖y i‖ ^ 2)⁻¹ ≤ D * (2 * Real.log 2 + 2 * ℓ) := by
    have hterm : ∀ i ∈ R.S j, Real.log (‖y i‖ ^ 2)⁻¹ ≤ 2 * Real.log 2 + 2 * ℓ := by
      intro i _
      rw [← PolyMaxLowerBound.log_inv_half_sq ht]
      have h2 : 0 < t / 2 := by linarith
      have hyi : 0 < ‖y i‖ := h2.trans_le (hyn i)
      apply Real.log_le_log (by positivity)
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ h2.le (hyn i) 2)
    have hM : 0 ≤ 2 * Real.log 2 + 2 * ℓ := by linarith
    calc ∑ i ∈ R.S j, Real.log (‖y i‖ ^ 2)⁻¹ ≤ ∑ i ∈ R.S j, (2 * Real.log 2 + 2 * ℓ) :=
          Finset.sum_le_sum hterm
      _ = (R.S j).card * (2 * Real.log 2 + 2 * ℓ) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ D * (2 * Real.log 2 + 2 * ℓ) := by
          apply mul_le_mul_of_nonneg_right _ hM
          have := Finset.card_le_univ (R.S j)
          rw [Fintype.card_fin] at this
          exact_mod_cast this
  have hrle : R.r ((R.chart j).symm y) ≤ Λ * ℓ := by
    rw [R.r_chart j y ⟨hyT, hyD⟩]
    have hf : R.f j y ≤ |B| := (le_abs_self _).trans ((hB j y hyT).trans (le_abs_self B))
    have hA : 0 ≤ Real.exp 1 + |B| + 2 * D * Real.log 2 := by
      have : 0 ≤ 2 * (D : ℝ) * Real.log 2 := by positivity
      have : 0 ≤ |B| := abs_nonneg B
      linarith
    have : Real.exp 1 + |B| + 2 * D * Real.log 2 ≤ (Real.exp 1 + |B| + 2 * D * Real.log 2) * ℓ :=
      le_mul_of_one_le_right hA hℓ1
    rw [hΛdef]
    nlinarith
  have hlogr : Real.log (R.r ((R.chart j).symm y)) ≤ Real.log Λ + Real.log ℓ := by
    rw [← Real.log_mul (by linarith) (by linarith)]
    exact Real.log_le_log (by linarith) hrle
  have hlogr0 : 0 ≤ Real.log (R.r ((R.chart j).symm y)) := Real.log_nonneg hr1
  have hph := R.ph_ge _ hYo

  have hq : -Q ≤ R.q j y := by
    have := (abs_le.1 (hqy.trans (hQj j))).1
    linarith
  have h1 : -(|R.Clog| * Real.log (R.r ((R.chart j).symm y))) ≤
      -R.Clog * Real.log (R.r ((R.chart j).symm y)) := by
    have := mul_le_mul_of_nonneg_right (le_abs_self R.Clog) hlogr0
    linarith
  have h2 : |R.Clog| * Real.log (R.r ((R.chart j).symm y)) ≤
      |R.Clog| * (Real.log Λ + 1) * Real.log ℓ := by
    have h3 : Real.log Λ + Real.log ℓ ≤ (Real.log Λ + 1) * Real.log ℓ := by nlinarith
    calc |R.Clog| * Real.log (R.r ((R.chart j).symm y)) ≤ |R.Clog| * (Real.log Λ + Real.log ℓ) :=
          mul_le_mul_of_nonneg_left hlogr (abs_nonneg _)
      _ ≤ |R.Clog| * ((Real.log Λ + 1) * Real.log ℓ) :=
          mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
      _ = _ := by ring
  have hQℓ : Q ≤ Q * Real.log ℓ := le_mul_of_one_le_right hQ0 hlogℓ
  have hu : -C * Real.log ℓ ≤ R.u j y := by
    show -C * Real.log ℓ ≤ R.q j y + R.ph ((R.chart j).symm y)
    rw [hCdef]
    nlinarith
  have htr : R.trunc K j y = max (R.u j y) (-K) := by
    simp only [RegChartData.trunc, limsupExt, if_neg hyD]

  unfold polyMax
  by_cases hb : BddAbove (R.trunc K j '' closedBall (R.chart j x) t)
  · refine le_trans ?_ (le_csSup hb (mem_image_of_mem _ hy))
    rw [htr]
    exact hu.trans (le_max_left _ _)
  · rw [Real.sSup_of_not_bddAbove hb]
    have : 0 ≤ C * Real.log ℓ := mul_nonneg hC0 (by linarith)
    linarith
end PolyMaxLowerBound
end GroundTheory.Heights₂.Heights.Regular
