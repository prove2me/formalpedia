-- Prove2me | solution 1 for TaoFivePrimes.eta_cutoff_model_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-09T09:46:57.327218+00:00
-- url     : https://prove2.me/submissions/d9c709bd-19ab-4de8-844d-a0efdc9357ed

import Definitions.Def_TaoFivePrimes_RepresentationCount
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

open MeasureTheory intervalIntegral

namespace TaoFivePrimes

private lemma infDist_cutoff_left {t : ℝ} (ht : t ≤ 1 / 5) :
    Metric.infDist t (Set.Icc (1 / 5 : ℝ) (4 / 5)) = 1 / 5 - t := by
  apply le_antisymm
  · calc
      Metric.infDist t (Set.Icc (1 / 5 : ℝ) (4 / 5))
          ≤ dist t (1 / 5 : ℝ) :=
        Metric.infDist_le_dist_of_mem (by constructor <;> norm_num)
      _ = 1 / 5 - t := by
        rw [Real.dist_eq, abs_of_nonpos (by linarith)]
        ring
  · rw [Metric.le_infDist (Set.nonempty_Icc.2 (by norm_num))]
    intro y hy
    rw [Real.dist_eq, abs_of_nonpos (by linarith [hy.1])]
    linarith [hy.1]

private lemma infDist_cutoff_middle {t : ℝ} (ht : t ∈ Set.Icc (1 / 5 : ℝ) (4 / 5)) :
    Metric.infDist t (Set.Icc (1 / 5 : ℝ) (4 / 5)) = 0 :=
  Metric.infDist_zero_of_mem ht

private lemma infDist_cutoff_right {t : ℝ} (ht : 4 / 5 ≤ t) :
    Metric.infDist t (Set.Icc (1 / 5 : ℝ) (4 / 5)) = t - 4 / 5 := by
  apply le_antisymm
  · calc
      Metric.infDist t (Set.Icc (1 / 5 : ℝ) (4 / 5))
          ≤ dist t (4 / 5 : ℝ) :=
        Metric.infDist_le_dist_of_mem (by constructor <;> norm_num)
      _ = t - 4 / 5 := by
        rw [Real.dist_eq, abs_of_nonneg (by linarith)]
  · rw [Metric.le_infDist (Set.nonempty_Icc.2 (by norm_num))]
    intro y hy
    rw [Real.dist_eq, abs_of_nonneg (by linarith [hy.2])]
    linarith [hy.2]

private lemma eta1_left_formula {t : ℝ} (htlo : 1 / 10 ≤ t) (hthi : t ≤ 1 / 5) :
    eta1 t = 10 * t - 1 := by
  unfold eta1
  rw [infDist_cutoff_left hthi, max_eq_right]
  · ring
  · linarith

private lemma eta1_middle_formula {t : ℝ} (ht : t ∈ Set.Icc (1 / 5 : ℝ) (4 / 5)) :
    eta1 t = 1 := by
  unfold eta1
  rw [infDist_cutoff_middle ht]
  norm_num

private lemma eta1_right_formula {t : ℝ} (htlo : 4 / 5 ≤ t) (hthi : t ≤ 9 / 10) :
    eta1 t = 9 - 10 * t := by
  unfold eta1
  rw [infDist_cutoff_right htlo, max_eq_right]
  · ring
  · linarith

private lemma eta1_eq_zero_of_le {t : ℝ} (ht : t ≤ 1 / 10) : eta1 t = 0 := by
  unfold eta1
  rw [infDist_cutoff_left (by linarith), max_eq_left]
  linarith

private lemma eta1_eq_zero_of_ge {t : ℝ} (ht : 9 / 10 ≤ t) : eta1 t = 0 := by
  unfold eta1
  rw [infDist_cutoff_right (by linarith), max_eq_left]
  linarith

private lemma eta1_nonneg (t : ℝ) : 0 ≤ eta1 t := by
  unfold eta1
  exact le_max_left _ _

private lemma eta1_le_one (t : ℝ) : eta1 t ≤ 1 := by
  unfold eta1
  apply max_le
  · norm_num
  · have h := Metric.infDist_nonneg (x := t) (s := Set.Icc (1 / 5 : ℝ) (4 / 5))
    linarith

private lemma eta1_continuous : Continuous eta1 := by
  unfold eta1
  fun_prop

private lemma eta1_lipschitz : LipschitzWith 10 eta1 := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, Real.dist_eq]
  unfold eta1
  have h := (Metric.lipschitz_infDist_pt (Set.Icc (1 / 5 : ℝ) (4 / 5))).norm_sub_le x y
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  calc
    |max 0 (1 - 10 * Metric.infDist x (Set.Icc (1 / 5 : ℝ) (4 / 5))) -
        max 0 (1 - 10 * Metric.infDist y (Set.Icc (1 / 5 : ℝ) (4 / 5)))|
        ≤ |(1 - 10 * Metric.infDist x (Set.Icc (1 / 5 : ℝ) (4 / 5))) -
            (1 - 10 * Metric.infDist y (Set.Icc (1 / 5 : ℝ) (4 / 5)))| :=
          by
            simpa [max_comm] using
              (abs_max_sub_max_le_abs
                (1 - 10 * Metric.infDist x (Set.Icc (1 / 5 : ℝ) (4 / 5)))
                (1 - 10 * Metric.infDist y (Set.Icc (1 / 5 : ℝ) (4 / 5))) 0)
    _ = 10 * |Metric.infDist x (Set.Icc (1 / 5 : ℝ) (4 / 5)) -
            Metric.infDist y (Set.Icc (1 / 5 : ℝ) (4 / 5))| := by
          rw [show (1 - 10 * Metric.infDist x (Set.Icc (1 / 5 : ℝ) (4 / 5))) -
              (1 - 10 * Metric.infDist y (Set.Icc (1 / 5 : ℝ) (4 / 5))) =
              -10 * (Metric.infDist x (Set.Icc (1 / 5 : ℝ) (4 / 5)) -
                Metric.infDist y (Set.Icc (1 / 5 : ℝ) (4 / 5))) by ring]
          rw [abs_mul]
          norm_num
    _ ≤ 10 * |x - y| := by
      have h' : |Metric.infDist x (Set.Icc (1 / 5 : ℝ) (4 / 5)) -
          Metric.infDist y (Set.Icc (1 / 5 : ℝ) (4 / 5))| ≤ |x - y| := by
        simpa using h
      exact mul_le_mul_of_nonneg_left h' (by norm_num)

private lemma eta1_symm (t : ℝ) : eta1 (1 - t) = eta1 t := by
  by_cases hlo : t ≤ 1 / 10
  · rw [eta1_eq_zero_of_le hlo, eta1_eq_zero_of_ge (by linarith)]
  by_cases hhi : 9 / 10 ≤ t
  · rw [eta1_eq_zero_of_ge hhi, eta1_eq_zero_of_le (by linarith)]
  by_cases hmidlo : t ≤ 1 / 5
  · rw [eta1_left_formula (by linarith) hmidlo,
      eta1_right_formula (by linarith) (by linarith)]
    ring
  by_cases hmidhi : 4 / 5 ≤ t
  · rw [eta1_right_formula hmidhi (by linarith),
      eta1_left_formula (by linarith) (by linarith)]
    ring
  · rw [eta1_middle_formula (by constructor <;> linarith),
      eta1_middle_formula (by constructor <;> linarith)]

private lemma eta1_support : Function.support eta1 ⊆ Set.Ioc (1 / 10) (9 / 10) := by
  intro t ht
  constructor
  · by_contra h
    exact ht (eta1_eq_zero_of_le (le_of_not_gt h))
  · by_contra h
    exact ht (eta1_eq_zero_of_ge (le_of_not_ge h))

private lemma eta1_sq_support :
    Function.support (fun t : ℝ => eta1 t ^ 2) ⊆ Set.Ioc (1 / 10) (9 / 10) := by
  intro t ht
  apply eta1_support
  intro h
  apply ht
  simp [h]

private lemma eta1_integrable : Integrable eta1 := by
  apply Continuous.integrable_of_hasCompactSupport eta1_continuous
  rw [HasCompactSupport]
  exact isCompact_Icc.closure_of_subset (eta1_support.trans Set.Ioc_subset_Icc_self)

private lemma eta1_integral : (∫ t : ℝ, eta1 t) = 7 / 10 := by
  have h₁ : IntervalIntegrable eta1 volume (1 / 10 : ℝ) (1 / 5 : ℝ) :=
    eta1_continuous.intervalIntegrable (μ := volume) _ _
  have h₂ : IntervalIntegrable eta1 volume (1 / 5 : ℝ) (4 / 5 : ℝ) :=
    eta1_continuous.intervalIntegrable (μ := volume) _ _
  have h₃ : IntervalIntegrable eta1 volume (4 / 5 : ℝ) (9 / 10 : ℝ) :=
    eta1_continuous.intervalIntegrable (μ := volume) _ _
  have h₁₂ : IntervalIntegrable eta1 volume (1 / 10 : ℝ) (4 / 5 : ℝ) := h₁.trans h₂
  calc
    (∫ t : ℝ, eta1 t) = ∫ t in (1 / 10 : ℝ)..(9 / 10 : ℝ), eta1 t :=
      (intervalIntegral.integral_eq_integral_of_support_subset eta1_support).symm
    _ = (∫ t in (1 / 10 : ℝ)..(1 / 5 : ℝ), eta1 t) +
          (∫ t in (1 / 5 : ℝ)..(4 / 5 : ℝ), eta1 t) +
          (∫ t in (4 / 5 : ℝ)..(9 / 10 : ℝ), eta1 t) := by
      rw [intervalIntegral.integral_add_adjacent_intervals h₁ h₂,
        intervalIntegral.integral_add_adjacent_intervals h₁₂ h₃]
    _ = (∫ t in (1 / 10 : ℝ)..(1 / 5 : ℝ), (10 * t - 1)) +
          (∫ _t in (1 / 5 : ℝ)..(4 / 5 : ℝ), (1 : ℝ)) +
          (∫ t in (4 / 5 : ℝ)..(9 / 10 : ℝ), (9 - 10 * t)) := by
      congr 1
      · congr 1
        · apply intervalIntegral.integral_congr
          intro t ht
          norm_num [Set.uIcc] at ht
          exact eta1_left_formula ht.1 ht.2
        · apply intervalIntegral.integral_congr
          intro t ht
          norm_num [Set.uIcc] at ht
          exact eta1_middle_formula ht
      · apply intervalIntegral.integral_congr
        intro t ht
        norm_num [Set.uIcc] at ht
        exact eta1_right_formula ht.1 ht.2
    _ = 7 / 10 := by
      ring_nf
      norm_num [integral_pow, integral_id]

private lemma integral_sq_affine (a b A B : ℝ) :
    (∫ x in a..b, (A * x + B) ^ 2) =
      (A ^ 2 / 3 * b ^ 3 + A * B * b ^ 2 + B ^ 2 * b) -
      (A ^ 2 / 3 * a ^ 3 + A * B * a ^ 2 + B ^ 2 * a) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    convert (((((hasDerivAt_id x).pow 3).const_mul (A ^ 2 / 3)).add
      (((hasDerivAt_id x).pow 2).const_mul (A * B))).add
      ((hasDerivAt_id x).const_mul (B ^ 2))) using 1
    · funext y
      simp
    · simp
      ring
  · exact (by fun_prop : Continuous (fun x : ℝ => (A * x + B) ^ 2)).intervalIntegrable
      (μ := volume) _ _

private lemma eta1_sq_integral : (∫ t : ℝ, eta1 t ^ 2) = 2 / 3 := by
  have hc : Continuous (fun t : ℝ => eta1 t ^ 2) := eta1_continuous.pow 2
  have h₁ : IntervalIntegrable (fun t : ℝ => eta1 t ^ 2) volume
      (1 / 10 : ℝ) (1 / 5 : ℝ) := hc.intervalIntegrable (μ := volume) _ _
  have h₂ : IntervalIntegrable (fun t : ℝ => eta1 t ^ 2) volume
      (1 / 5 : ℝ) (4 / 5 : ℝ) := hc.intervalIntegrable (μ := volume) _ _
  have h₃ : IntervalIntegrable (fun t : ℝ => eta1 t ^ 2) volume
      (4 / 5 : ℝ) (9 / 10 : ℝ) := hc.intervalIntegrable (μ := volume) _ _
  have h₁₂ : IntervalIntegrable (fun t : ℝ => eta1 t ^ 2) volume
      (1 / 10 : ℝ) (4 / 5 : ℝ) := h₁.trans h₂
  calc
    (∫ t : ℝ, eta1 t ^ 2) = ∫ t in (1 / 10 : ℝ)..(9 / 10 : ℝ), eta1 t ^ 2 :=
      (intervalIntegral.integral_eq_integral_of_support_subset eta1_sq_support).symm
    _ = (∫ t in (1 / 10 : ℝ)..(1 / 5 : ℝ), eta1 t ^ 2) +
          (∫ t in (1 / 5 : ℝ)..(4 / 5 : ℝ), eta1 t ^ 2) +
          (∫ t in (4 / 5 : ℝ)..(9 / 10 : ℝ), eta1 t ^ 2) := by
      rw [intervalIntegral.integral_add_adjacent_intervals h₁ h₂,
        intervalIntegral.integral_add_adjacent_intervals h₁₂ h₃]
    _ = (∫ t in (1 / 10 : ℝ)..(1 / 5 : ℝ), (10 * t - 1) ^ 2) +
          (∫ _t in (1 / 5 : ℝ)..(4 / 5 : ℝ), (1 : ℝ)) +
          (∫ t in (4 / 5 : ℝ)..(9 / 10 : ℝ), (9 - 10 * t) ^ 2) := by
      congr 1
      · congr 1
        · apply intervalIntegral.integral_congr
          intro t ht
          change eta1 t ^ 2 = (10 * t - 1) ^ 2
          norm_num [Set.uIcc] at ht
          rw [eta1_left_formula ht.1 ht.2]
        · apply intervalIntegral.integral_congr
          intro t ht
          change eta1 t ^ 2 = (1 : ℝ)
          norm_num [Set.uIcc] at ht
          rw [eta1_middle_formula ht]
          norm_num
      · apply intervalIntegral.integral_congr
        intro t ht
        change eta1 t ^ 2 = (9 - 10 * t) ^ 2
        norm_num [Set.uIcc] at ht
        rw [eta1_right_formula ht.1 ht.2]
    _ = 2 / 3 := by
      rw [show (fun t : ℝ => (10 * t - 1) ^ 2) =
          (fun t : ℝ => (10 * t + (-1)) ^ 2) by funext t; ring,
        show (fun t : ℝ => (9 - 10 * t) ^ 2) =
          (fun t : ℝ => ((-10) * t + 9) ^ 2) by funext t; ring,
        integral_sq_affine, integral_sq_affine]
      simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]
      norm_num

private lemma eta0_nonneg (t : ℝ) : 0 ≤ eta0 t := by
  unfold eta0
  split_ifs <;> positivity

private lemma log_half : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]

private lemma log_quarter : Real.log (1 / 4 : ℝ) = -2 * Real.log 2 := by
  rw [show (1 / 4 : ℝ) = ((2 : ℝ)⁻¹) ^ 2 by norm_num, Real.log_pow, Real.log_inv]
  norm_num

private lemma eta0_eq_zero_of_le {t : ℝ} (ht : t ≤ 1 / 4) : eta0 t = 0 := by
  unfold eta0
  split_ifs with hpos
  · have hlog : Real.log (2 * t) ≤ Real.log (1 / 2 : ℝ) := by
      exact Real.log_le_log (by positivity) (by linarith)
    rw [log_half] at hlog
    have hneg : Real.log 2 ≤ -Real.log (2 * t) := by linarith
    have hcut : Real.log 2 - |Real.log (2 * t)| ≤ 0 :=
      sub_nonpos.mpr (hneg.trans (neg_le_abs (Real.log (2 * t))))
    rw [max_eq_left hcut, mul_zero]
  · rfl

private lemma eta0_eq_zero_of_ge {t : ℝ} (ht : 1 ≤ t) : eta0 t = 0 := by
  unfold eta0
  rw [if_pos (by linarith)]
  have hlog : Real.log 2 ≤ Real.log (2 * t) := by
    exact Real.log_le_log (by norm_num) (by linarith)
  have hcut : Real.log 2 - |Real.log (2 * t)| ≤ 0 :=
    sub_nonpos.mpr (hlog.trans (le_abs_self (Real.log (2 * t))))
  rw [max_eq_left hcut, mul_zero]

private lemma eta0_left_formula {t : ℝ} (htlo : 1 / 4 ≤ t) (hthi : t ≤ 1 / 2) :
    eta0 t = 4 * (2 * Real.log 2 + Real.log t) := by
  unfold eta0
  rw [if_pos (by linarith), abs_of_nonpos]
  · rw [max_eq_right]
    · rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : t ≠ 0)]
      ring
    · have hlog : Real.log (1 / 2 : ℝ) ≤ Real.log (2 * t) := by
        exact Real.log_le_log (by norm_num) (by linarith)
      rw [log_half] at hlog
      linarith
  · exact Real.log_nonpos (by positivity) (by linarith)

private lemma eta0_right_formula {t : ℝ} (htlo : 1 / 2 ≤ t) (hthi : t ≤ 1) :
    eta0 t = -4 * Real.log t := by
  unfold eta0
  rw [if_pos (by linarith), abs_of_nonneg]
  · rw [max_eq_right]
    · rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : t ≠ 0)]
      ring
    · have hlog : Real.log (2 * t) ≤ Real.log 2 := by
        exact Real.log_le_log (by positivity) (by linarith)
      linarith
  · exact Real.log_nonneg (by linarith)

private lemma eta0_support : Function.support eta0 ⊆ Set.Ioc (1 / 4) 1 := by
  intro t ht
  constructor
  · by_contra h
    exact ht (eta0_eq_zero_of_le (le_of_not_gt h))
  · by_contra h
    exact ht (eta0_eq_zero_of_ge (le_of_not_ge h))

private lemma eta0_integrable : Integrable eta0 := by
  have hleft_formula : Set.EqOn eta0 (fun t : ℝ => 4 * (2 * Real.log 2 + Real.log t))
      (Set.uIcc (1 / 4 : ℝ) (1 / 2 : ℝ)) := by
    intro t ht
    norm_num [Set.uIcc] at ht
    exact eta0_left_formula ht.1 ht.2
  have hright_formula : Set.EqOn eta0 (fun t : ℝ => -4 * Real.log t)
      (Set.uIcc (1 / 2 : ℝ) 1) := by
    intro t ht
    norm_num [Set.uIcc] at ht
    exact eta0_right_formula ht.1 ht.2
  have hleft : IntervalIntegrable eta0 volume (1 / 4 : ℝ) (1 / 2 : ℝ) := by
    rw [intervalIntegrable_congr (hleft_formula.mono Set.uIoc_subset_uIcc)]
    exact ((intervalIntegrable_const.add intervalIntegrable_log').const_mul 4)
  have hright : IntervalIntegrable eta0 volume (1 / 2 : ℝ) 1 := by
    rw [intervalIntegrable_congr (hright_formula.mono Set.uIoc_subset_uIcc)]
    exact intervalIntegrable_log'.const_mul (-4)
  have hwhole : IntervalIntegrable eta0 volume (1 / 4 : ℝ) 1 := hleft.trans hright
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at hwhole
  exact (integrableOn_iff_integrable_of_support_subset eta0_support).mp hwhole

private lemma eta0_integral : (∫ t : ℝ, eta0 t) = 1 := by
  have hleft_formula : Set.EqOn eta0 (fun t : ℝ => 4 * (2 * Real.log 2 + Real.log t))
      (Set.uIcc (1 / 4 : ℝ) (1 / 2 : ℝ)) := by
    intro t ht
    norm_num [Set.uIcc] at ht
    exact eta0_left_formula ht.1 ht.2
  have hright_formula : Set.EqOn eta0 (fun t : ℝ => -4 * Real.log t)
      (Set.uIcc (1 / 2 : ℝ) 1) := by
    intro t ht
    norm_num [Set.uIcc] at ht
    exact eta0_right_formula ht.1 ht.2
  have hleft : IntervalIntegrable eta0 volume (1 / 4 : ℝ) (1 / 2 : ℝ) := by
    rw [intervalIntegrable_congr (hleft_formula.mono Set.uIoc_subset_uIcc)]
    exact ((intervalIntegrable_const.add intervalIntegrable_log').const_mul 4)
  have hright : IntervalIntegrable eta0 volume (1 / 2 : ℝ) 1 := by
    rw [intervalIntegrable_congr (hright_formula.mono Set.uIoc_subset_uIcc)]
    exact intervalIntegrable_log'.const_mul (-4)
  calc
    (∫ t : ℝ, eta0 t) = ∫ t in (1 / 4 : ℝ)..1, eta0 t :=
      (intervalIntegral.integral_eq_integral_of_support_subset eta0_support).symm
    _ = (∫ t in (1 / 4 : ℝ)..(1 / 2 : ℝ), eta0 t) +
        ∫ t in (1 / 2 : ℝ)..1, eta0 t := by
      rw [intervalIntegral.integral_add_adjacent_intervals hleft hright]
    _ = (∫ t in (1 / 4 : ℝ)..(1 / 2 : ℝ),
          4 * (2 * Real.log 2 + Real.log t)) +
        ∫ t in (1 / 2 : ℝ)..1, -4 * Real.log t := by
      rw [intervalIntegral.integral_congr hleft_formula,
        intervalIntegral.integral_congr hright_formula]
    _ = 1 := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add intervalIntegrable_const intervalIntegrable_log',
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
        integral_log, integral_log]
      simp only [smul_eq_mul]
      rw [log_half, log_quarter, Real.log_one]
      ring

private lemma eta1_hasCompactSupport : HasCompactSupport eta1 := by
  rw [HasCompactSupport]
  exact isCompact_Icc.closure_of_subset (eta1_support.trans Set.Ioc_subset_Icc_self)

private lemma eta1_product_integrable (t : ℝ) :
    Integrable (fun s : ℝ => eta1 s * eta1 (1 - s - t / 1000)) := by
  have hc : Continuous (fun s : ℝ => eta1 s * eta1 (1 - s - t / 1000)) :=
    eta1_continuous.mul (eta1_continuous.comp
      ((continuous_const.sub continuous_id).sub continuous_const))
  have hs : HasCompactSupport (fun s : ℝ => eta1 s * eta1 (1 - s - t / 1000)) := by
    change HasCompactSupport (eta1 * fun s : ℝ => eta1 (1 - s - t / 1000))
    exact eta1_hasCompactSupport.mul_right
  exact hc.integrable_of_hasCompactSupport hs

private noncomputable def cutoffSlice (t : ℝ) : ℝ :=
  ∫ s : ℝ, eta1 s * eta1 (1 - s - t / 1000)

private lemma cutoffSlice_zero : cutoffSlice 0 = 2 / 3 := by
  simp only [cutoffSlice, zero_div, sub_zero, eta1_symm, ← pow_two]
  exact eta1_sq_integral

private lemma cutoffSlice_bound (t : ℝ) : |cutoffSlice t| ≤ 7 / 10 := by
  have h := MeasureTheory.norm_integral_le_of_norm_le
    (f := fun s : ℝ => eta1 s * eta1 (1 - s - t / 1000)) (g := eta1)
    eta1_integrable
    (Filter.Eventually.of_forall (fun s : ℝ => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (eta1_nonneg s), abs_of_nonneg (eta1_nonneg _)]
      exact mul_le_of_le_one_right (eta1_nonneg s) (eta1_le_one _)))
  simpa only [cutoffSlice, Real.norm_eq_abs, eta1_integral] using h

private lemma cutoffSlice_lipschitz : LipschitzWith (7 / 1000) cutoffSlice := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  have hxi := eta1_product_integrable x
  have hyi := eta1_product_integrable y
  simp only [cutoffSlice]
  rw [← integral_sub hxi hyi]
  have hbound : ∀ s : ℝ,
      ‖eta1 s * eta1 (1 - s - x / 1000) - eta1 s * eta1 (1 - s - y / 1000)‖ ≤
        eta1 s * ((10 / 1000 : ℝ) * |x - y|) := by
    intro s
    have hlip := eta1_lipschitz.norm_sub_le
      (1 - s - x / 1000) (1 - s - y / 1000)
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hlip
    have hshift : |eta1 (1 - s - x / 1000) - eta1 (1 - s - y / 1000)| ≤
        (10 / 1000 : ℝ) * |x - y| := by
      calc
        |eta1 (1 - s - x / 1000) - eta1 (1 - s - y / 1000)|
            ≤ 10 * |(1 - s - x / 1000) - (1 - s - y / 1000)| := by
              simpa using hlip
        _ = (10 / 1000 : ℝ) * |x - y| := by
          rw [show (1 - s - x / 1000) - (1 - s - y / 1000) = (y - x) / 1000 by ring,
            abs_div, abs_sub_comm]
          norm_num
          ring
    rw [show eta1 s * eta1 (1 - s - x / 1000) - eta1 s * eta1 (1 - s - y / 1000) =
      eta1 s * (eta1 (1 - s - x / 1000) - eta1 (1 - s - y / 1000)) by ring,
      Real.norm_eq_abs, abs_mul, abs_of_nonneg (eta1_nonneg s)]
    exact mul_le_mul_of_nonneg_left hshift (eta1_nonneg s)
  have hnorm := MeasureTheory.norm_integral_le_of_norm_le
    (f := fun s : ℝ =>
      eta1 s * eta1 (1 - s - x / 1000) - eta1 s * eta1 (1 - s - y / 1000))
    (g := fun s : ℝ => eta1 s * ((10 / 1000 : ℝ) * |x - y|))
    (eta1_integrable.mul_const ((10 / 1000 : ℝ) * |x - y|))
    (Filter.Eventually.of_forall hbound)
  calc
    ‖∫ s : ℝ,
        eta1 s * eta1 (1 - s - x / 1000) - eta1 s * eta1 (1 - s - y / 1000)‖
        ≤ ∫ s : ℝ, eta1 s * ((10 / 1000 : ℝ) * |x - y|) := hnorm
    _ = (7 / 10 : ℝ) * ((10 / 1000 : ℝ) * |x - y|) := by
      rw [MeasureTheory.integral_mul_const, eta1_integral]
    _ = ((7 / 1000 : NNReal) : ℝ) * |x - y| := by
      norm_num
      ring

private lemma cutoffSlice_shift_bound {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |cutoffSlice t - 2 / 3| ≤ 7 / 1000 := by
  rw [← cutoffSlice_zero]
  have h := cutoffSlice_lipschitz.norm_sub_le t 0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, abs_of_nonneg ht0] at h
  calc
    |cutoffSlice t - cutoffSlice 0| ≤ (7 / 1000 : ℝ) * t := by simpa using h
    _ ≤ 7 / 1000 := by nlinarith

private lemma cutoffSlice_integrable_mul_eta0 :
    Integrable (fun t : ℝ => cutoffSlice t * eta0 t) := by
  have hmeas : AEStronglyMeasurable cutoffSlice volume :=
    cutoffSlice_lipschitz.continuous.aestronglyMeasurable
  have hbd : ∀ᵐ t : ℝ ∂volume, ‖cutoffSlice t‖ ≤ (7 / 10 : ℝ) :=
    Filter.Eventually.of_forall (fun t => by simpa [Real.norm_eq_abs] using cutoffSlice_bound t)
  have h := eta0_integrable.bdd_mul hmeas hbd
  simpa [mul_comm] using h

private lemma real_cutoff_mass_bound :
    |(∫ t : ℝ, cutoffSlice t * eta0 t) - 2 / 3| ≤ 7 / 1000 := by
  have hconst : (∫ t : ℝ, (2 / 3 : ℝ) * eta0 t) = 2 / 3 := by
    rw [MeasureTheory.integral_const_mul, eta0_integral, mul_one]
  rw [← hconst, ← integral_sub cutoffSlice_integrable_mul_eta0
    (eta0_integrable.const_mul (2 / 3 : ℝ))]
  have hdom : Integrable (fun t : ℝ => (7 / 1000 : ℝ) * eta0 t) :=
    eta0_integrable.const_mul (7 / 1000 : ℝ)
  have hpoint : ∀ t : ℝ,
      ‖cutoffSlice t * eta0 t - (2 / 3 : ℝ) * eta0 t‖ ≤
        (7 / 1000 : ℝ) * eta0 t := by
    intro t
    by_cases ht : t ∈ Set.Ioc (1 / 4 : ℝ) 1
    · rw [show cutoffSlice t * eta0 t - (2 / 3 : ℝ) * eta0 t =
          (cutoffSlice t - 2 / 3) * eta0 t by ring,
        Real.norm_eq_abs, abs_mul, abs_of_nonneg (eta0_nonneg t)]
      exact mul_le_mul_of_nonneg_right
        (cutoffSlice_shift_bound (by linarith [ht.1]) ht.2) (eta0_nonneg t)
    · have hz : eta0 t = 0 := by
        by_contra hne
        exact ht (eta0_support hne)
      simp [hz]
  have hnorm := MeasureTheory.norm_integral_le_of_norm_le
    (f := fun t : ℝ => cutoffSlice t * eta0 t - (2 / 3 : ℝ) * eta0 t)
    (g := fun t : ℝ => (7 / 1000 : ℝ) * eta0 t)
    hdom (Filter.Eventually.of_forall hpoint)
  change ‖∫ t : ℝ, cutoffSlice t * eta0 t - (2 / 3 : ℝ) * eta0 t‖ ≤ 7 / 1000
  calc
    ‖∫ t : ℝ, cutoffSlice t * eta0 t - (2 / 3 : ℝ) * eta0 t‖
        ≤ ∫ t : ℝ, (7 / 1000 : ℝ) * eta0 t := hnorm
    _ = 7 / 1000 := by rw [MeasureTheory.integral_const_mul, eta0_integral, mul_one]

private lemma complex_cutoff_eq_real :
    (∫ t : ℝ, ∫ s : ℝ,
      (((eta1 s * eta1 (1 - s - t / 1000) * eta0 t : ℝ) : ℂ))) =
      (((∫ t : ℝ, cutoffSlice t * eta0 t) : ℝ) : ℂ) := by
  calc
    (∫ t : ℝ, ∫ s : ℝ,
      (((eta1 s * eta1 (1 - s - t / 1000) * eta0 t : ℝ) : ℂ))) =
        ∫ t : ℝ, (((∫ s : ℝ,
          eta1 s * eta1 (1 - s - t / 1000) * eta0 t) : ℝ) : ℂ) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with t
      exact _root_.integral_ofReal
    _ = ∫ t : ℝ, ((cutoffSlice t * eta0 t : ℝ) : ℂ) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with t
      congr 1
      rw [MeasureTheory.integral_mul_const]
      rfl
    _ = (((∫ t : ℝ, cutoffSlice t * eta0 t) : ℝ) : ℂ) := _root_.integral_ofReal

end TaoFivePrimes

open TaoFivePrimes

theorem solution :
    let cutoffCoefficient : ℂ :=
      ∫ t : ℝ, ∫ s : ℝ,
        (((eta1 s * eta1 (1 - s - t / 1000) * eta0 t : ℝ) : ℂ))
    ‖cutoffCoefficient - (((2 / 3 : ℝ) : ℂ))‖ ≤ 1 / 100 := by
  dsimp only
  rw [complex_cutoff_eq_real, ← Complex.ofReal_sub, Complex.norm_real]
  exact real_cutoff_mass_bound.trans (by norm_num)

#print axioms solution


