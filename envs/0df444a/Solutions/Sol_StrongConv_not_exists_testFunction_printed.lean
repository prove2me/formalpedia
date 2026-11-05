-- Prove2me | solution 1 for StrongConv.not_exists_testFunction_printed
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-04T23:29:48.270949+00:00
-- url     : https://prove2.me/submissions/e0e75cd7-c067-4d4c-a26a-1982a0104fc4

import Mathlib
import Definitions.Def_StrongConv

open Filter Topology Polynomial MeasureTheory

namespace StrongConv

lemma fcontdiff (χ : ℝ → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun θ => χ (2 * Real.cos θ)) :=
  hχ.comp (contDiff_const.mul Real.contDiff_cos)

lemma cont_deriv (χ : ℝ → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) :
    Continuous (deriv (fun θ => χ (2 * Real.cos θ))) :=
  (fcontdiff χ hχ).continuous_deriv (by exact_mod_cast le_top)

lemma piece (χ : ℝ → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) {a b : ℝ} (hab : a ≤ b) :
    |(χ (2 * Real.cos b)) - χ (2 * Real.cos a)| ≤
      ∫ θ in a..b, |deriv (fun θ => χ (2 * Real.cos θ)) θ| := by
  have hd : Differentiable ℝ (fun θ => χ (2 * Real.cos θ)) :=
    (fcontdiff χ hχ).differentiable (by simp)
  have hc := cont_deriv χ hχ
  have := intervalIntegral.integral_deriv_eq_sub (f := fun θ => χ (2 * Real.cos θ))
    (a := a) (b := b) (fun x _ => hd x) (hc.intervalIntegrable a b)
  rw [← this]
  exact intervalIntegral.abs_integral_le_integral_abs hab

lemma variation_ge (χ : ℝ → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (h0 : χ 0 = 0) (h2 : χ 2 = 1)
    (hm2 : χ (-2) = 1) :
    4 ≤ ∫ θ in (0 : ℝ)..2 * Real.pi, |deriv (fun θ => χ (2 * Real.cos θ)) θ| := by
  have hc := cont_deriv χ hχ
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun θ => |deriv (fun θ => χ (2 * Real.cos θ)) θ|)
      MeasureTheory.volume a b := fun a b => (hc.abs).intervalIntegrable a b
  have hpi := Real.pi_pos
  have p1 := piece χ hχ (a := 0) (b := Real.pi / 2) (by positivity)
  have p2 := piece χ hχ (a := Real.pi / 2) (b := Real.pi) (by linarith)
  have p3 := piece χ hχ (a := Real.pi) (b := 3 * Real.pi / 2) (by linarith)
  have p4 := piece χ hχ (a := 3 * Real.pi / 2) (b := 2 * Real.pi) (by linarith)
  have c1 : Real.cos (3 * Real.pi / 2) = 0 := by
    have : 3 * Real.pi / 2 = Real.pi / 2 + Real.pi := by ring
    rw [this, Real.cos_add_pi]; simp
  simp only [Real.cos_zero, Real.cos_pi_div_two, Real.cos_pi, c1, Real.cos_two_pi, mul_one,
    mul_zero, mul_neg, h0, h2, hm2] at p1 p2 p3 p4
  have e := intervalIntegral.integral_add_adjacent_intervals (hi 0 (Real.pi / 2)) (hi (Real.pi / 2) Real.pi)
  have e2 := intervalIntegral.integral_add_adjacent_intervals (hi 0 Real.pi) (hi Real.pi (3 * Real.pi / 2))
  have e3 := intervalIntegral.integral_add_adjacent_intervals (hi 0 (3 * Real.pi / 2)) (hi (3 * Real.pi / 2) (2 * Real.pi))
  norm_num at p1 p2 p3 p4
  linarith


lemma holder_step (g : ℝ → ℝ) (hc : Continuous g) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, |g θ|) ≤
      lpNormCircle (4 / 3) g * (2 * Real.pi) ^ ((1 : ℝ) / 4) := by
  set μ : Measure ℝ := volume.restrict (Set.Icc 0 (2 * Real.pi)) with hμ
  haveI : IsFiniteMeasure μ := ⟨by rw [hμ, Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  have hpi := Real.pi_pos
  have hmeas : AEStronglyMeasurable g μ := hc.aestronglyMeasurable
  have hmem : MemLp g (ENNReal.ofReal (4 / 3)) μ := by
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * Real.pi)).exists_bound_of_continuousOn
      hc.continuousOn
    refine MemLp.of_bound hmeas M ?_
    rw [hμ]
    exact (ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall hM)
  have hint : Integrable g μ := hmem.integrable (by
    rw [ENNReal.one_le_ofReal]; norm_num)
  have hA : eLpNorm g 1 μ = ENNReal.ofReal (∫ θ in (0 : ℝ)..2 * Real.pi, |g θ|) := by
    rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm hint]
    congr 1
    rw [intervalIntegral.integral_of_le (by positivity), hμ,
      MeasureTheory.integral_Icc_eq_integral_Ioc]
    simp [Real.norm_eq_abs]
  have hh := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ) (p := 1)
    (q := ENNReal.ofReal (4 / 3)) (by rw [ENNReal.one_le_ofReal]; norm_num) hmeas
  have hU : μ Set.univ = ENNReal.ofReal (2 * Real.pi) := by
    rw [hμ, Measure.restrict_apply_univ, Real.volume_Icc]; simp
  have ht : (1 : ENNReal).toReal = 1 := by simp
  have hq : (ENNReal.ofReal (4 / 3)).toReal = 4 / 3 := ENNReal.toReal_ofReal (by norm_num)
  rw [hA, hU, ht, hq] at hh
  have hfin : eLpNorm g (ENNReal.ofReal (4 / 3)) μ ≠ ⊤ := hmem.eLpNorm_ne_top
  have hexp : (1 / (1 : ℝ) - 1 / (4 / 3)) = 1 / 4 := by norm_num
  rw [hexp] at hh
  have hrhs : eLpNorm g (ENNReal.ofReal (4 / 3)) μ * ENNReal.ofReal (2 * Real.pi) ^ ((1 : ℝ) / 4) ≠ ⊤ :=
    ENNReal.mul_ne_top hfin (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
  have := ENNReal.toReal_mono hrhs hh
  rw [ENNReal.toReal_ofReal (by
    apply intervalIntegral.integral_nonneg (by positivity); intros; exact abs_nonneg _),
    ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (by positivity)] at this
  exact this


lemma rpow_quarter_lt {x : ℝ} (hx : 0 ≤ x) (h : x < 16) : x ^ ((1 : ℝ) / 4) < 2 := by
  have h16 : (16 : ℝ) ^ ((1 : ℝ) / 4) = 2 := by
    have := Real.pow_rpow_inv_natCast (x := 2) (n := 4) (by norm_num) (by norm_num)
    norm_num at this ⊢
  rw [← h16]
  exact Real.rpow_lt_rpow hx h (by norm_num)

theorem not_exists_testFunction_dev :
    ¬ ∃ C : ℝ, ∀ (m : ℕ) (K ρ ε : ℝ), 0 < K → 0 < ρ → 0 < ε → ρ + ε < K →
      ∃ χ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ (∀ x, χ x ∈ Set.Icc 0 1) ∧
        (∀ x, |x| ≤ ρ + ε / 2 → χ x = 0) ∧ (∀ x, ρ + ε ≤ |x| → χ x = 1) ∧
        ∀ β : ℝ, 1 < β →
          lpNormCircle β (iteratedDeriv (m + 1) (fun θ => χ (K * Real.cos θ))) ≤
            (C * m) ^ m * (K / ε) ^ ((m : ℝ) + 1 / conjExp β) := by
  rintro ⟨C, H⟩
  obtain ⟨χ, hχ, -, h0, h1, hb⟩ := H 0 2 (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have e0 : χ 0 = 0 := h0 0 (by norm_num)
  have e2 : χ 2 = 1 := h1 2 (by rw [abs_of_pos (by norm_num)]; norm_num)
  have em2 : χ (-2) = 1 := h1 (-2) (by rw [abs_neg, abs_of_pos (by norm_num)]; norm_num)
  have hb := hb (4 / 3) (by norm_num)
  have hconj : conjExp (4 / 3) = 4 := by unfold conjExp; norm_num
  rw [hconj, zero_add, iteratedDeriv_one] at hb
  have hbase : ((2 : ℝ) / (1 / 2)) = 4 := by norm_num
  simp only [Nat.cast_zero, zero_mul, pow_zero, one_mul, zero_add, hbase] at hb
  have hlow := variation_ge χ hχ e0 e2 em2
  have hh := holder_step _ (cont_deriv χ hχ)
  have hpi : Real.pi < 4 := Real.pi_lt_four
  set L := lpNormCircle (4 / 3) (deriv fun θ => χ (2 * Real.cos θ)) with hL
  have hL0 : 0 ≤ L := ENNReal.toReal_nonneg
  have h4 : (4 : ℝ) ^ ((1 : ℝ) / 4) < 2 := rpow_quarter_lt (by norm_num) (by norm_num)
  have h2pi : (2 * Real.pi) ^ ((1 : ℝ) / 4) < 2 := rpow_quarter_lt (by positivity) (by linarith)
  have : L * (2 * Real.pi) ^ ((1 : ℝ) / 4) < 4 := by
    have hpos : 0 < (2 * Real.pi) ^ ((1 : ℝ) / 4) := by positivity
    calc L * (2 * Real.pi) ^ ((1 : ℝ) / 4) ≤ 4 ^ ((1 : ℝ) / 4) * (2 * Real.pi) ^ ((1 : ℝ) / 4) :=
          by gcongr
      _ < 2 * 2 := by gcongr
      _ = 4 := by norm_num
  linarith

end StrongConv

theorem solution : type_of% @StrongConv.not_exists_testFunction_dev := @StrongConv.not_exists_testFunction_dev
