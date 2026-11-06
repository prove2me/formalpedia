-- Prove2me | solution 1 for TabooRegen.chernoff_tail
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T14:19:35.132215+00:00
-- url     : https://prove2.me/submissions/202b1c05-3d4b-47e7-a0d4-7d3e4ced4bba

import Mathlib
import Definitions.Def_TabooRegen_Window

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace TabooRegen.ChernoffAux

/-- `e^x ≤ 1 + x + x² e^x` for `x ≥ 0`. -/
lemma exp_le_quad {x : ℝ} (hx : 0 ≤ x) :
    Real.exp x ≤ 1 + x + x ^ 2 * Real.exp x := by
  have h1 : 1 - x ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
  have h2 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  have hpos : 0 < Real.exp x := Real.exp_pos x
  have e1 : Real.exp x ≤ 1 + x * Real.exp x := by
    have := mul_le_mul_of_nonneg_left h1 hpos.le
    nlinarith
  have e2 : x * Real.exp x ≤ x * (1 + x * Real.exp x) := mul_le_mul_of_nonneg_left e1 hx
  nlinarith

/-- For `y ≥ 0`, `0 ≤ ε ≤ ε₀/2`: `e^{εy} ≤ 1 + εy + ε² (8/ε₀²) e^{ε₀ y}`. -/
lemma exp_pointwise {ε ε₀ y : ℝ} (hε : 0 ≤ ε) (hε₀ : 0 < ε₀) (hεε : ε ≤ ε₀ / 2) (hy : 0 ≤ y) :
    Real.exp (ε * y) ≤ 1 + ε * y + ε ^ 2 * ((8 / ε₀ ^ 2) * Real.exp (ε₀ * y)) := by
  have hx : 0 ≤ ε * y := mul_nonneg hε hy
  have hA := exp_le_quad hx
  set z := ε₀ * y / 2 with hz
  have hz0 : 0 ≤ z := by positivity
  have hq := Real.quadratic_le_exp_of_nonneg hz0
  have hz2 : z ^ 2 ≤ 2 * Real.exp z := by nlinarith
  have hmono : Real.exp (ε * y) ≤ Real.exp z := by
    apply Real.exp_le_exp.mpr
    rw [hz]; nlinarith
  have hyz : y = 2 * z / ε₀ := by rw [hz]; field_simp
  have hez : Real.exp (ε₀ * y) = Real.exp z * Real.exp z := by
    rw [← Real.exp_add]; congr 1; rw [hz]; ring
  -- y² e^{εy} ≤ (8/ε₀²) e^{ε₀ y}
  have hkey : y ^ 2 * Real.exp (ε * y) ≤ (8 / ε₀ ^ 2) * Real.exp (ε₀ * y) := by
    have hy2 : y ^ 2 = 4 * z ^ 2 / ε₀ ^ 2 := by rw [hyz]; field_simp; ring
    rw [hy2, hez]
    have hez0 : 0 < Real.exp z := Real.exp_pos z
    have hε2 : 0 < ε₀ ^ 2 := by positivity
    have step1 : 4 * z ^ 2 / ε₀ ^ 2 * Real.exp (ε * y) ≤ 4 * z ^ 2 / ε₀ ^ 2 * Real.exp z :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    have step2 : 4 * z ^ 2 / ε₀ ^ 2 * Real.exp z ≤ 4 * (2 * Real.exp z) / ε₀ ^ 2 * Real.exp z := by
      apply mul_le_mul_of_nonneg_right _ hez0.le
      apply div_le_div_of_nonneg_right _ hε2.le
      linarith
    have step3 : 4 * (2 * Real.exp z) / ε₀ ^ 2 * Real.exp z = 8 / ε₀ ^ 2 * (Real.exp z * Real.exp z) := by
      ring
    linarith
  have : (ε * y) ^ 2 * Real.exp (ε * y) ≤ ε ^ 2 * ((8 / ε₀ ^ 2) * Real.exp (ε₀ * y)) := by
    rw [mul_pow, mul_assoc]
    exact mul_le_mul_of_nonneg_left hkey (sq_nonneg ε)
  linarith

/-- The moment generating function of `convPow F ℓ` is the `ℓ`-th power. -/
lemma lintegral_exp_convPow (F : Measure ℝ) [IsProbabilityMeasure F] (ε : ℝ) :
    ∀ ℓ : ℕ, ∫⁻ y, ENNReal.ofReal (Real.exp (ε * y)) ∂(QueueingFundamentals.MG1.convPow F ℓ) =
      (∫⁻ y, ENNReal.ofReal (Real.exp (ε * y)) ∂F) ^ ℓ := by
  have hmeas : Measurable fun y : ℝ => ENNReal.ofReal (Real.exp (ε * y)) := by fun_prop
  intro ℓ
  induction ℓ with
  | zero =>
    simp [QueueingFundamentals.MG1.convPow, lintegral_dirac]
  | succ n ih =>
    rw [QueueingFundamentals.MG1.convPow, Measure.lintegral_conv hmeas, pow_succ, ← ih,
      ← lintegral_mul_const _ hmeas]
    apply lintegral_congr
    intro x
    rw [← lintegral_const_mul _ hmeas]
    apply lintegral_congr
    intro y
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, mul_add]

/-- Chernoff bound. -/
lemma chernoff_part1 (F : Measure ℝ) [IsProbabilityMeasure F] (ε : ℝ) (hε : 0 ≤ ε) (ℓ : ℕ)
    (x : ℝ) : QueueingFundamentals.MG1.convPow F ℓ (Set.Ioi x) ≤
      ENNReal.ofReal (Real.exp (-ε * x)) * (∫⁻ y, ENNReal.ofReal (Real.exp (ε * y)) ∂F) ^ ℓ := by
  have hmeas : Measurable fun y : ℝ => ENNReal.ofReal (Real.exp (ε * y)) := by fun_prop
  rw [← lintegral_exp_convPow F ε ℓ, ← lintegral_const_mul _ hmeas,
    ← lintegral_indicator_one measurableSet_Ioi]
  apply lintegral_mono
  intro y
  by_cases hy : y ∈ Set.Ioi x
  · dsimp only
    rw [Set.indicator_of_mem hy, Pi.one_apply, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← Real.exp_add]
    have : 0 ≤ -ε * x + ε * y := by
      have : x < y := hy
      nlinarith
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by simpa using Real.one_le_exp this)
  · rw [Set.indicator_of_notMem hy]
    exact bot_le

end TabooRegen.ChernoffAux

open MeasureTheory TabooRegen in
theorem solution (F : Measure ℝ) [IsProbabilityMeasure F] (hF : F (Set.Iio 0) = 0)
    (hexp : ∃ ε₀ > 0, ∫⁻ x, ENNReal.ofReal (Real.exp (ε₀ * x)) ∂F < ⊤) :
    (∀ ε : ℝ, 0 ≤ ε → ∀ (ℓ : ℕ) (x : ℝ), QueueingFundamentals.MG1.convPow F ℓ (Set.Ioi x) ≤
        ENNReal.ofReal (Real.exp (-ε * x)) * (∫⁻ y, ENNReal.ofReal (Real.exp (ε * y)) ∂F) ^ ℓ) ∧
    ∀ η : ℝ, 0 < η → η < 1 → ∃ δ > 0, ∀ (ℓ : ℕ) (t : ℝ), 0 ≤ t →
      (SmithRegenerative.Equilibrium.mean F).toReal * ℓ ≤ (1 - η) * t →
        QueueingFundamentals.MG1.convPow F ℓ (Set.Ioi ((1 - η / 2) * t)) ≤
          ENNReal.ofReal (Real.exp (-δ * t)) := by
  refine ⟨fun ε hε ℓ x => ChernoffAux.chernoff_part1 F ε hε ℓ x, ?_⟩
  intro η hη0 hη1
  obtain ⟨ε₀, hε₀, hfin⟩ := hexp
  have hnn : ∀ᵐ y ∂F, 0 ≤ y := by
    rw [ae_iff]
    have : {a : ℝ | ¬ 0 ≤ a} = Set.Iio 0 := by ext a; simp
    rw [this, hF]
  -- integrability of e^{ε₀ y}
  have hint0 : Integrable (fun y => Real.exp (ε₀ * y)) F := by
    have := integrable_toReal_of_lintegral_ne_top
      (f := fun y => ENNReal.ofReal (Real.exp (ε₀ * y))) (by fun_prop) hfin.ne
    simpa [ENNReal.toReal_ofReal (Real.exp_pos _).le] using this
  have hintId : Integrable (fun y : ℝ => y) F := by
    refine Integrable.mono' (hint0.const_mul (1 / ε₀)) (by fun_prop) ?_
    filter_upwards [hnn] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg hy]
    have h1 := Real.add_one_le_exp (ε₀ * y)
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hε₀]
    linarith [mul_comm y ε₀]
  have hintE : ∀ ε, 0 ≤ ε → ε ≤ ε₀ → Integrable (fun y => Real.exp (ε * y)) F := by
    intro ε hε hεε
    refine Integrable.mono' hint0 (by fun_prop) ?_
    filter_upwards [hnn] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hεε hy)
  have hMeq : ∀ ε, 0 ≤ ε → ε ≤ ε₀ → ∫⁻ y, ENNReal.ofReal (Real.exp (ε * y)) ∂F =
      ENNReal.ofReal (∫ y, Real.exp (ε * y) ∂F) := by
    intro ε hε hεε
    rw [ofReal_integral_eq_lintegral_ofReal (hintE ε hε hεε)
      (Filter.Eventually.of_forall fun y => (Real.exp_pos _).le)]
  -- the mean
  set m := (SmithRegenerative.Equilibrium.mean F).toReal with hm
  have hmean : m = ∫ y, y ∂F := by
    rw [hm, SmithRegenerative.Equilibrium.mean,
      integral_eq_lintegral_of_nonneg_ae hnn hintId.aestronglyMeasurable]
  have hm0 : 0 ≤ m := by rw [hm]; exact ENNReal.toReal_nonneg
  rcases hm0.eq_or_lt with hmz | hmpos
  · -- mean zero: `y = 0` a.e.
    have hy0 : ∀ᵐ y ∂F, y = 0 := by
      have hzero : ∫ y, y ∂F = 0 := by rw [← hmean, ← hmz]
      have := (integral_eq_zero_iff_of_nonneg_ae hnn hintId).mp hzero
      filter_upwards [this] with y hy
      simpa using hy
    have hM1 : ∫⁻ y, ENNReal.ofReal (Real.exp (1 * y)) ∂F = 1 := by
      rw [lintegral_congr_ae (g := fun _ => 1)]
      · simp
      · filter_upwards [hy0] with y hy
        simp [hy]
    refine ⟨1 - η / 2, by linarith, ?_⟩
    intro ℓ t ht _
    have := ChernoffAux.chernoff_part1 F 1 zero_le_one ℓ ((1 - η / 2) * t)
    rw [hM1, one_pow, mul_one] at this
    refine this.trans (le_of_eq ?_)
    congr 2
    ring
  · -- positive mean
    set I0 := ∫ y, Real.exp (ε₀ * y) ∂F with hI0
    have hI0pos : 0 < I0 := by
      rw [hI0]
      exact integral_exp_pos hint0
    set D := 8 / ε₀ ^ 2 * I0 with hD
    have hDpos : 0 < D := by positivity
    set ε := min (ε₀ / 2) (η * m / (4 * D)) with hεdef
    have hεpos : 0 < ε := lt_min (by linarith) (by positivity)
    have hεle : ε ≤ ε₀ / 2 := min_le_left _ _
    have hεD : ε * D ≤ η * m / 4 := by
      have := min_le_right (ε₀ / 2) (η * m / (4 * D))
      rw [← hεdef] at this
      calc ε * D ≤ η * m / (4 * D) * D := mul_le_mul_of_nonneg_right this hDpos.le
        _ = η * m / 4 := by field_simp
    -- `I(ε) ≤ 1 + ε m + ε² D`
    set Ie := ∫ y, Real.exp (ε * y) ∂F with hIe
    have hIe_le : Ie ≤ 1 + ε * m + ε ^ 2 * D := by
      have i1 : Integrable (fun y : ℝ => 1 + ε * y) F := (integrable_const 1).add (hintId.const_mul ε)
      have i2 : Integrable (fun y => ε ^ 2 * (8 / ε₀ ^ 2 * Real.exp (ε₀ * y))) F :=
        (hint0.const_mul _).const_mul _
      have hb : Integrable (fun y => 1 + ε * y + ε ^ 2 * ((8 / ε₀ ^ 2) * Real.exp (ε₀ * y))) F :=
        i1.add i2
      have hle := integral_mono_ae (hintE ε hεpos.le (by linarith)) hb (by
        filter_upwards [hnn] with y hy
        exact ChernoffAux.exp_pointwise hεpos.le hε₀ hεle hy)
      have hcalc : ∫ y, (1 + ε * y + ε ^ 2 * ((8 / ε₀ ^ 2) * Real.exp (ε₀ * y))) ∂F =
          1 + ε * m + ε ^ 2 * D := by
        rw [integral_add i1 i2, integral_add (integrable_const 1) (hintId.const_mul ε),
          integral_const_mul, integral_const_mul, integral_const_mul, integral_const, hmean, hD, hI0]
        simp
      rw [hIe]; linarith
    have hIe0 : 0 ≤ Ie := integral_nonneg fun y => (Real.exp_pos _).le
    refine ⟨ε * η / 4, by positivity, ?_⟩
    intro ℓ t ht hℓ
    have hP := ChernoffAux.chernoff_part1 F ε hεpos.le ℓ ((1 - η / 2) * t)
    rw [hMeq ε hεpos.le (by linarith), ← ENNReal.ofReal_pow hIe0,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le] at hP
    refine hP.trans (ENNReal.ofReal_le_ofReal ?_)
    set a := ε * m + ε ^ 2 * D with ha
    have ha0 : 0 ≤ a := by positivity
    have hpow : Ie ^ ℓ ≤ Real.exp (ℓ * a) := by
      calc Ie ^ ℓ ≤ (1 + a) ^ ℓ := pow_le_pow_left₀ hIe0 (by linarith) ℓ
        _ ≤ (Real.exp a) ^ ℓ := pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp a]) ℓ
        _ = Real.exp (ℓ * a) := by rw [← Real.exp_nat_mul]
    have hℓ0 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
    -- ℓ a ≤ ε(1-η)t + ε(η/4)t
    have hmℓ : m * ℓ ≤ (1 - η) * t := hℓ
    have k1 : ε * (m * ℓ) ≤ ε * ((1 - η) * t) := mul_le_mul_of_nonneg_left hmℓ hεpos.le
    have k2 : (ε * D) * ℓ ≤ (η * m / 4) * ℓ := mul_le_mul_of_nonneg_right hεD hℓ0
    have k3 : (η / 4) * (m * ℓ) ≤ (η / 4) * ((1 - η) * t) :=
      mul_le_mul_of_nonneg_left hmℓ (by positivity)
    have k4 : (η / 4) * ((1 - η) * t) ≤ (η / 4) * t := by
      have : (1 - η) * t ≤ t := by nlinarith
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have k5 : ε * ((ε * D) * ℓ) ≤ ε * ((η / 4) * t) := by
      apply mul_le_mul_of_nonneg_left _ hεpos.le
      calc (ε * D) * ℓ ≤ (η * m / 4) * ℓ := k2
        _ = (η / 4) * (m * ℓ) := by ring
        _ ≤ (η / 4) * t := k3.trans k4
    have hla : ℓ * a ≤ ε * ((1 - η) * t) + ε * ((η / 4) * t) := by
      have : ℓ * a = ε * (m * ℓ) + ε * ((ε * D) * ℓ) := by rw [ha]; ring
      rw [this]; linarith
    calc Real.exp (-ε * ((1 - η / 2) * t)) * Ie ^ ℓ
        ≤ Real.exp (-ε * ((1 - η / 2) * t)) * Real.exp (ℓ * a) :=
          mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
      _ = Real.exp (-ε * ((1 - η / 2) * t) + ℓ * a) := by rw [Real.exp_add]
      _ ≤ Real.exp (-(ε * η / 4) * t) := by
          apply Real.exp_le_exp.mpr
          have : -(ε * η / 4) * t = -ε * ((1 - η / 2) * t) + (ε * ((1 - η) * t) + ε * ((η / 4) * t)) := by
            ring
          rw [this]; linarith
