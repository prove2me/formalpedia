-- Prove2me | solution 1 for RobustMeanCov.OnePoint.robust_objective_concave_monotone_second_deriv
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T00:01:56.698053+00:00
-- url     : https://prove2.me/submissions/510f90cf-8820-432b-836a-40cacfb60d35

import Mathlib
import Definitions.Def_RobustMeanCov_Shared_MeanVarClass
import Definitions.Def_RobustMeanCov_OnePoint_OnePointSupport
open MeasureTheory Filter Topology

set_option autoImplicit false

theorem rmc_refl (u : ℝ → ℝ) (hu : Differentiable ℝ u) (hu' : Differentiable ℝ (deriv u)) :
    Differentiable ℝ (fun y => u (-y)) ∧
    deriv (fun y => u (-y)) = (fun y => - deriv u (-y)) ∧
    Differentiable ℝ (deriv (fun y => u (-y))) ∧
    deriv (deriv (fun y => u (-y))) = (fun y => deriv (deriv u) (-y)) := by
  have h1 : deriv (fun y => u (-y)) = (fun y => - deriv u (-y)) := by
    funext y; exact deriv_comp_neg (f := u) (x := y)
  refine ⟨by fun_prop, h1, ?_, ?_⟩
  · rw [h1]; fun_prop
  · rw [h1]
    funext y
    have : deriv (fun y => -deriv u (-y)) y = - deriv (fun y => deriv u (-y)) y := by
      exact deriv.fun_neg
    rw [this, deriv_comp_neg]; simp

theorem rmc_taylor_left_upper (u : ℝ → ℝ) (hu : Differentiable ℝ u)
    (hu' : Differentiable ℝ (deriv u)) (k M : ℝ) (h : ∀ t ≤ M, deriv (deriv u) t ≤ k) :
    ∀ y ≤ M, u y ≤ u M + deriv u M * (y - M) + k * (y - M) ^ 2 / 2 := by
  have h1 : ∀ y ≤ M, deriv u M + k * (y - M) ≤ deriv u y := by
    have hd : ∀ x, HasDerivAt (fun y => deriv u y - k * y) (deriv (deriv u) x - k) x := by
      intro x
      have hk : HasDerivAt (fun y : ℝ => k * y) k x :=
        ((hasDerivAt_id' x).const_mul k).congr_deriv (mul_one k)
      exact (hu' x).hasDerivAt.sub hk
    have hanti : AntitoneOn (fun y => deriv u y - k * y) (Set.Iic M) := by
      apply antitoneOn_of_deriv_nonpos (convex_Iic M)
      · exact fun x _ => (hd x).continuousAt.continuousWithinAt
      · exact fun x _ => (hd x).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Iic] at hx
        rw [(hd x).deriv]
        linarith [h x (le_of_lt hx)]
    intro y hy
    have := hanti hy (Set.mem_Iic.2 le_rfl) hy
    simp only at this
    linarith
  have hd2 : ∀ x, HasDerivAt (fun y => u y - deriv u M * y - k * (y - M) ^ 2 / 2)
      (deriv u x - deriv u M - k * (x - M)) x := by
    intro x
    have h3 : HasDerivAt (fun y => (y - M) * (y - M)) ((x - M) + (x - M)) x := by
      have h0 : HasDerivAt (fun y : ℝ => y - M) 1 x := (hasDerivAt_id' x).sub_const M
      exact (h0.mul h0).congr_deriv (by ring)
    have h4 : HasDerivAt (fun y : ℝ => deriv u M * y) (deriv u M) x :=
      ((hasDerivAt_id' x).const_mul (deriv u M)).congr_deriv (mul_one _)
    have h5 : HasDerivAt (fun y => k * ((y - M) * (y - M)) / 2) (k * ((x - M) + (x - M)) / 2) x :=
      (h3.const_mul k).div_const 2
    have h6 := ((hu x).hasDerivAt.sub h4).sub h5
    have e : (fun y => u y - deriv u M * y - k * (y - M) ^ 2 / 2) =
        (fun y => u y - deriv u M * y - k * ((y - M) * (y - M)) / 2) := by
      funext y; ring
    rw [e]
    exact h6.congr_deriv (by ring)
  have hmono : MonotoneOn (fun y => u y - deriv u M * y - k * (y - M) ^ 2 / 2) (Set.Iic M) := by
    apply monotoneOn_of_deriv_nonneg (convex_Iic M)
    · exact fun x _ => (hd2 x).continuousAt.continuousWithinAt
    · exact fun x _ => (hd2 x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Iic] at hx
      rw [(hd2 x).deriv]
      linarith [h1 x (le_of_lt hx)]
  intro y hy
  have := hmono hy (Set.mem_Iic.2 le_rfl) hy
  simp only at this
  nlinarith [this]

theorem rmc_taylor_left_lower (u : ℝ → ℝ) (hu : Differentiable ℝ u)
    (hu' : Differentiable ℝ (deriv u)) (k M : ℝ) (h : ∀ t ≤ M, k ≤ deriv (deriv u) t) :
    ∀ y ≤ M, u M + deriv u M * (y - M) + k * (y - M) ^ 2 / 2 ≤ u y := by
  have hn : deriv (fun y => -u y) = fun y => - deriv u y := by
    funext y; exact deriv.fun_neg
  have hn2 : deriv (deriv (fun y => -u y)) = fun y => - deriv (deriv u) y := by
    rw [hn]; funext y; exact deriv.fun_neg
  have := rmc_taylor_left_upper (fun y => -u y) hu.neg (by rw [hn]; exact hu'.neg) (-k) M
    (by
      intro t ht
      rw [hn2]
      have := h t ht
      simp only
      linarith)
  intro y hy
  have h2 := this y hy
  rw [hn] at h2
  simp only at h2
  nlinarith [h2]

theorem rmc_taylor_right_upper (u : ℝ → ℝ) (hu : Differentiable ℝ u)
    (hu' : Differentiable ℝ (deriv u)) (k M : ℝ) (h : ∀ t ≥ M, deriv (deriv u) t ≤ k) :
    ∀ y ≥ M, u y ≤ u M + deriv u M * (y - M) + k * (y - M) ^ 2 / 2 := by
  obtain ⟨hv, hv1, hv2, hv3⟩ := rmc_refl u hu hu'
  have := rmc_taylor_left_upper (fun y => u (-y)) hv hv2 k (-M)
    (by
      intro t ht
      rw [hv3]
      exact h (-t) (by linarith))
  intro y hy
  have h2 := this (-y) (by linarith)
  rw [hv1] at h2
  simp only [neg_neg] at h2
  nlinarith [h2]

theorem rmc_taylor_right_lower (u : ℝ → ℝ) (hu : Differentiable ℝ u)
    (hu' : Differentiable ℝ (deriv u)) (k M : ℝ) (h : ∀ t ≥ M, k ≤ deriv (deriv u) t) :
    ∀ y ≥ M, u M + deriv u M * (y - M) + k * (y - M) ^ 2 / 2 ≤ u y := by
  obtain ⟨hv, hv1, hv2, hv3⟩ := rmc_refl u hu hu'
  have := rmc_taylor_left_lower (fun y => u (-y)) hv hv2 k (-M)
    (by
      intro t ht
      rw [hv3]
      exact h (-t) (by linarith))
  intro y hy
  have h2 := this (-y) (by linarith)
  rw [hv1] at h2
  simp only [neg_neg] at h2
  nlinarith [h2]

theorem rmc_global_lower (u : ℝ → ℝ) (hu : Differentiable ℝ u)
    (hu' : Differentiable ℝ (deriv u)) (L : ℝ) (hL : ∀ t, L ≤ deriv (deriv u) t) (m y : ℝ) :
    u m + deriv u m * (y - m) + L * (y - m) ^ 2 / 2 ≤ u y := by
  rcases le_total y m with h | h
  · exact rmc_taylor_left_lower u hu hu' L m (fun t _ => hL t) y h
  · exact rmc_taylor_right_lower u hu hu' L m (fun t _ => hL t) y h

theorem rmc_global_upper (u : ℝ → ℝ) (hu : Differentiable ℝ u)
    (hu' : Differentiable ℝ (deriv u)) (h0 : ∀ t, deriv (deriv u) t ≤ 0) (m y : ℝ) :
    u y ≤ u m + deriv u m * (y - m) := by
  rcases le_total y m with h | h
  · have := rmc_taylor_left_upper u hu hu' 0 m (fun t _ => h0 t) y h
    simpa using this
  · have := rmc_taylor_right_upper u hu hu' 0 m (fun t _ => h0 t) y h
    simpa using this

open RobustMeanCov.Shared in
theorem rmc_core_L (u : ℝ → ℝ) (hu : Differentiable ℝ u)
    (hu' : Differentiable ℝ (deriv u)) (L : ℝ) (hL : ∀ t, L ≤ deriv (deriv u) t)
    (h0 : ∀ t, deriv (deriv u) t ≤ 0) (m s : ℝ) (ν : Measure ℝ)
    (hν : ν ∈ MeanVarClass m (s ^ 2)) :
    Integrable u ν ∧ u m + L * s ^ 2 / 2 ≤ ∫ y, u y ∂ν := by
  obtain ⟨hprob, hmem, hmean, hvar⟩ := hν
  have hint1 : Integrable (fun y : ℝ => y) ν := hmem.integrable (by norm_num)
  have hint2 : Integrable (fun y : ℝ => (y - m) ^ 2) ν := by
    have := (hmem.sub (memLp_const m)).integrable_sq
    simpa using this
  have hint3 : Integrable (fun y : ℝ => y - m) ν := hint1.sub (integrable_const m)
  have hq : Integrable (fun y : ℝ => u m + deriv u m * (y - m) + L * (y - m) ^ 2 / 2) ν :=
    ((integrable_const (u m)).add (hint3.const_mul (deriv u m))).add
      ((hint2.const_mul L).div_const 2)
  have hl : Integrable (fun y : ℝ => u m + deriv u m * (y - m)) ν :=
    (integrable_const (u m)).add (hint3.const_mul (deriv u m))
  have e1 : ∫ y, (y - m) ∂ν = 0 := by
    rw [integral_sub hint1 (integrable_const m)]
    simp [hmean]
  have hqint : ∫ y, (u m + deriv u m * (y - m) + L * (y - m) ^ 2 / 2) ∂ν
      = u m + L * s ^ 2 / 2 := by
    have hl2 : Integrable (fun y : ℝ => L * (y - m) ^ 2 / 2) ν := (hint2.const_mul L).div_const 2
    have hl3 : Integrable (fun y : ℝ => deriv u m * (y - m)) ν := hint3.const_mul (deriv u m)
    have e2 : ∫ y, (u m + deriv u m * (y - m) + L * (y - m) ^ 2 / 2) ∂ν =
        ∫ y, (u m + deriv u m * (y - m)) ∂ν + ∫ y, L * (y - m) ^ 2 / 2 ∂ν := integral_add hl hl2
    have e3 : ∫ y, (u m + deriv u m * (y - m)) ∂ν = ∫ _y, u m ∂ν + ∫ y, deriv u m * (y - m) ∂ν :=
      integral_add (integrable_const (u m)) hl3
    have e4 : ∫ y, L * (y - m) ^ 2 / 2 ∂ν = L * s ^ 2 / 2 := by
      rw [integral_div, integral_const_mul, hvar]
    have e5 : ∫ y, deriv u m * (y - m) ∂ν = 0 := by
      rw [integral_const_mul, e1, mul_zero]
    rw [e2, e3, e4, e5]
    simp
  have hmeas : AEStronglyMeasurable u ν := hu.continuous.aestronglyMeasurable
  have hu_int : Integrable u ν := by
    refine Integrable.mono' (hq.norm.add hl.norm) hmeas (Eventually.of_forall fun y => ?_)
    have h1 := rmc_global_lower u hu hu' L hL m y
    have h2 := rmc_global_upper u hu hu' h0 m y
    rw [Real.norm_eq_abs]
    have h3 := neg_abs_le (u m + deriv u m * (y - m) + L * (y - m) ^ 2 / 2)
    have h4 := le_abs_self (u m + deriv u m * (y - m))
    have h5 := abs_nonneg (u m + deriv u m * (y - m) + L * (y - m) ^ 2 / 2)
    have h6 := abs_nonneg (u m + deriv u m * (y - m))
    show |u y| ≤ ‖u m + deriv u m * (y - m) + L * (y - m) ^ 2 / 2‖ + ‖u m + deriv u m * (y - m)‖
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    rw [abs_le]
    constructor <;> linarith
  refine ⟨hu_int, ?_⟩
  rw [← hqint]
  exact integral_mono hq hu_int (fun y => rmc_global_lower u hu hu' L hL m y)

open RobustMeanCov.Shared in
theorem rmc_two_point (m s p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ ν ∈ MeanVarClass m (s ^ 2), ∀ f : ℝ → ℝ, Continuous f → Integrable f ν ∧
      ∫ y, f y ∂ν = p * f (m + √((1 - p) / p) * s) + (1 - p) * f (m - √(p / (1 - p)) * s) := by
  set a : ℝ := √((1 - p) / p) * s with ha
  set b : ℝ := √(p / (1 - p)) * s with hb
  have hq0 : 0 < 1 - p := by linarith
  set ν : Measure ℝ := ENNReal.ofReal p • Measure.dirac (m + a)
    + ENNReal.ofReal (1 - p) • Measure.dirac (m - b) with hν
  have hgen : ∀ f : ℝ → ℝ, Continuous f → Integrable f ν ∧
      ∫ y, f y ∂ν = p * f (m + a) + (1 - p) * f (m - b) := by
    intro f hf
    have i1 : Integrable f (ENNReal.ofReal p • Measure.dirac (m + a)) :=
      (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
    have i2 : Integrable f (ENNReal.ofReal (1 - p) • Measure.dirac (m - b)) :=
      (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
    refine ⟨i1.add_measure i2, ?_⟩
    rw [hν, integral_add_measure i1 i2, integral_smul_measure, integral_smul_measure,
      integral_dirac, integral_dirac, ENNReal.toReal_ofReal hp0.le,
      ENNReal.toReal_ofReal hq0.le]
    simp
  -- algebraic identities
  set r : ℝ := √((1 - p) / p) with hr
  set t : ℝ := √(p / (1 - p)) with ht
  have hr2 : r ^ 2 = (1 - p) / p := Real.sq_sqrt (by positivity)
  have ht2 : t ^ 2 = p / (1 - p) := Real.sq_sqrt (by positivity)
  have hrt : r * t = 1 := by
    rw [hr, ht, ← Real.sqrt_mul (by positivity)]
    have : (1 - p) / p * (p / (1 - p)) = 1 := by field_simp
    rw [this, Real.sqrt_one]
  have hpr : p * r = (1 - p) * t := by
    have h1 : (1 - p) * t ^ 2 = p := by rw [ht2]; field_simp
    calc p * r = (1 - p) * t ^ 2 * r := by rw [h1]
      _ = (1 - p) * t * (r * t) := by ring
      _ = (1 - p) * t := by rw [hrt, mul_one]
  have hpr2 : p * r ^ 2 = 1 - p := by rw [hr2]; field_simp
  have hqt2 : (1 - p) * t ^ 2 = p := by rw [ht2]; field_simp
  have hmean : p * (m + a) + (1 - p) * (m - b) = m := by
    rw [ha, hb]
    linear_combination s * hpr
  have hvar : p * ((m + a) - m) ^ 2 + (1 - p) * ((m - b) - m) ^ 2 = s ^ 2 := by
    rw [ha, hb]
    linear_combination s ^ 2 * hpr2 + s ^ 2 * hqt2
  refine ⟨ν, ⟨?_, ?_, ?_, ?_⟩, hgen⟩
  · constructor
    rw [hν]
    simp only [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem
      (Set.mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add hp0.le hq0.le]
    have : p + (1 - p) = 1 := by ring
    rw [this]; simp
  · have hs2 : Integrable (fun y : ℝ => y ^ 2) ν := (hgen (fun y => y ^ 2) (by fun_prop)).1
    exact (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2 hs2
  · have := (hgen (fun y => y) continuous_id).2
    rw [this]; exact hmean
  · have := (hgen (fun y => (y - m) ^ 2) (by fun_prop)).2
    rw [this]; exact hvar

open RobustMeanCov.OnePoint in
theorem rmc_tail_upper (u : ℝ → ℝ) (hu : Continuous u) (m s : ℝ) (hs : 0 < s)
    (M c2 α β : ℝ) (h : ∀ y ≤ M, u y ≤ c2 / 2 * y ^ 2 + α * y + β) :
    ∃ F : ℝ → ℝ, (∀ᶠ p in 𝓝[<] (1 : ℝ), twoPointValue u m s p ≤ F p) ∧
      Tendsto F (𝓝[<] (1 : ℝ)) (𝓝 (u m + c2 * s ^ 2 / 2)) := by
  refine ⟨fun p => p * u (m + √((1 - p) / p) * s) +
    (c2 / 2 * ((1 - p) * m ^ 2 - 2 * m * s * √(p * (1 - p)) + s ^ 2 * p)
      + α * ((1 - p) * m - s * √(p * (1 - p))) + β * (1 - p)), ?_, ?_⟩
  · set X : ℝ := max ((m - M) / s) 0 with hX
    have hX0 : 0 ≤ X := le_max_right _ _
    have hp0 : X ^ 2 / (1 + X ^ 2) < 1 := by
      rw [div_lt_one (by positivity)]; linarith
    have hev : Set.Ioo (X ^ 2 / (1 + X ^ 2)) 1 ∈ 𝓝[<] (1 : ℝ) := Ioo_mem_nhdsLT hp0
    filter_upwards [hev] with p hp
    obtain ⟨hpa, hpb⟩ := hp
    have hpos : 0 < p := lt_of_le_of_lt (by positivity) hpa
    have hq0 : 0 < 1 - p := by linarith
    set t : ℝ := √(p / (1 - p)) with ht
    have ht2 : t ^ 2 = p / (1 - p) := Real.sq_sqrt (by positivity)
    have hqt2 : (1 - p) * t ^ 2 = p := by rw [ht2]; field_simp
    have he1 : (1 - p) * t = √(p * (1 - p)) := by
      have : p * (1 - p) = (1 - p) ^ 2 * (p / (1 - p)) := by field_simp
      rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hq0.le]
    have hXt : X ≤ t := by
      rw [ht]
      apply Real.le_sqrt_of_sq_le
      rw [le_div_iff₀ hq0]
      rw [div_lt_iff₀ (by positivity)] at hpa
      nlinarith
    have hmt : m - t * s ≤ M := by
      have h1 : (m - M) / s ≤ X := le_max_left _ _
      rw [div_le_iff₀ hs] at h1
      nlinarith
    have h2 := h (m - t * s) hmt
    have h3 : (1 - p) * u (m - t * s) ≤
        (1 - p) * (c2 / 2 * (m - t * s) ^ 2 + α * (m - t * s) + β) :=
      mul_le_mul_of_nonneg_left h2 hq0.le
    have h4 : (1 - p) * (c2 / 2 * (m - t * s) ^ 2 + α * (m - t * s) + β) =
        c2 / 2 * ((1 - p) * m ^ 2 - 2 * m * s * √(p * (1 - p)) + s ^ 2 * p)
          + α * ((1 - p) * m - s * √(p * (1 - p))) + β * (1 - p) := by
      linear_combination (c2 / 2 * (-2 * m * s) - α * s) * he1 + (c2 / 2 * s ^ 2) * hqt2
    simp only [RobustMeanCov.OnePoint.twoPointValue]
    linarith
  · have hc : ContinuousAt (fun p : ℝ => p * u (m + √((1 - p) / p) * s) +
      (c2 / 2 * ((1 - p) * m ^ 2 - 2 * m * s * √(p * (1 - p)) + s ^ 2 * p)
        + α * ((1 - p) * m - s * √(p * (1 - p))) + β * (1 - p))) 1 := by
      have hs1 : ContinuousAt (fun p : ℝ => √((1 - p) / p)) 1 :=
        (((continuous_const.sub continuous_id).continuousAt).div continuousAt_id
          one_ne_zero).sqrt
      have hs2 : ContinuousAt (fun p : ℝ => √(p * (1 - p))) 1 :=
        ((continuous_id.mul (continuous_const.sub continuous_id)).continuousAt).sqrt
      have hu1 : ContinuousAt (fun p : ℝ => u (m + √((1 - p) / p) * s)) 1 :=
        (hu.continuousAt).comp (continuousAt_const.add (hs1.mul continuousAt_const))
      have hs3 : Continuous (fun p : ℝ => √(p * (1 - p))) := by fun_prop
      have hrest : Continuous (fun p : ℝ =>
          c2 / 2 * ((1 - p) * m ^ 2 - 2 * m * s * √(p * (1 - p)) + s ^ 2 * p)
            + α * ((1 - p) * m - s * √(p * (1 - p))) + β * (1 - p)) := by fun_prop
      have hfin := (continuousAt_id.mul hu1).add hrest.continuousAt
      exact hfin
    have := hc.tendsto
    have h1 := this.mono_left (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))
    convert h1 using 2
    simp
    ring

open RobustMeanCov.OnePoint in
theorem rmc_refl_tpv (u : ℝ → ℝ) (m s p : ℝ) :
    twoPointValue u m s p = twoPointValue (fun y => u (-y)) (-m) s (1 - p) := by
  simp only [twoPointValue]
  have : 1 - (1 - p) = p := by ring
  rw [this]
  have e1 : -(-m + √(p / (1 - p)) * s) = m - √(p / (1 - p)) * s := by ring
  have e2 : -(-m - √((1 - p) / p) * s) = m + √((1 - p) / p) * s := by ring
  rw [e1, e2]
  ring

open RobustMeanCov.OnePoint in
theorem rmc_coreA (u : ℝ → ℝ) (hu : Differentiable ℝ u)
    (hu' : Differentiable ℝ (deriv u)) (L : ℝ) (hL : ∀ t, L ≤ deriv (deriv u) t)
    (h0 : ∀ t, deriv (deriv u) t ≤ 0)
    (hlim : Tendsto (deriv (deriv u)) atBot (𝓝 L)) (m s : ℝ) (hs : 0 ≤ s) :
    Tendsto (twoPointValue u m s) (𝓝[<] (1 : ℝ)) (𝓝 (u m + L * s ^ 2 / 2)) := by
  rcases hs.eq_or_lt with h | hs
  · subst h
    have : twoPointValue u m 0 = fun _ => u m := by
      funext p; simp [twoPointValue]; ring
    rw [this]
    simp
  · rw [tendsto_order]
    constructor
    · intro a' ha'
      have hev : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) := Ioo_mem_nhdsLT one_pos
      filter_upwards [hev] with p hp
      obtain ⟨ν, hν, hν2⟩ := rmc_two_point m s p hp.1 hp.2
      have h1 := (rmc_core_L u hu hu' L hL h0 m s ν hν).2
      have h2 := (hν2 u hu.continuous).2
      simp only [twoPointValue]
      linarith
    · intro a' ha'
      set T := u m + L * s ^ 2 / 2 with hT
      have hs2 : 0 < s ^ 2 + 1 := by positivity
      set ε : ℝ := (a' - T) / (s ^ 2 + 1) with hε
      have hε0 : 0 < ε := div_pos (by linarith) hs2
      obtain ⟨M, hM⟩ := eventually_atBot.1 (hlim.eventually (gt_mem_nhds (show L < L + ε by linarith)))
      have htay := rmc_taylor_left_upper u hu hu' (L + ε) M (fun t ht => (hM t ht).le)
      have hb : ∀ y ≤ M, u y ≤ (L + ε) / 2 * y ^ 2 + (deriv u M - (L + ε) * M) * y
          + (u M - deriv u M * M + (L + ε) * M ^ 2 / 2) := by
        intro y hy
        have := htay y hy
        nlinarith [this]
      obtain ⟨F, hF1, hF2⟩ := rmc_tail_upper u hu.continuous m s hs M (L + ε)
        (deriv u M - (L + ε) * M) (u M - deriv u M * M + (L + ε) * M ^ 2 / 2) hb
      have hlt : u m + (L + ε) * s ^ 2 / 2 < a' := by
        have : ε * (s ^ 2 + 1) = a' - T := by rw [hε]; field_simp
        nlinarith [sq_nonneg s]
      have hev2 := hF2.eventually (gt_mem_nhds hlt)
      filter_upwards [hF1, hev2] with p h1 h2
      linarith

open RobustMeanCov.OnePoint in
theorem rmc_coreB (u : ℝ → ℝ) (hu : Differentiable ℝ u)
    (hu' : Differentiable ℝ (deriv u))
    (hlim : Tendsto (deriv (deriv u)) atBot atBot) (m s : ℝ) (hs : 0 < s) (C : ℝ) :
    ∃ p : ℝ, 0 < p ∧ p < 1 ∧ twoPointValue u m s p < C := by
  set K : ℝ := 2 * (|u m - C| + 1) / s ^ 2 with hK
  have hs2 : 0 < s ^ 2 := by positivity
  have hKs : K * s ^ 2 / 2 = |u m - C| + 1 := by rw [hK]; field_simp
  obtain ⟨M, hM⟩ := eventually_atBot.1 (hlim.eventually (eventually_le_atBot (-K)))
  have htay := rmc_taylor_left_upper u hu hu' (-K) M (fun t ht => hM t ht)
  have hb : ∀ y ≤ M, u y ≤ (-K) / 2 * y ^ 2 + (deriv u M - (-K) * M) * y
      + (u M - deriv u M * M + (-K) * M ^ 2 / 2) := by
    intro y hy
    have := htay y hy
    nlinarith [this]
  obtain ⟨F, hF1, hF2⟩ := rmc_tail_upper u hu.continuous m s hs M (-K)
    (deriv u M - (-K) * M) (u M - deriv u M * M + (-K) * M ^ 2 / 2) hb
  have hlt : u m + (-K) * s ^ 2 / 2 < C := by
    have h1 := neg_abs_le (u m - C)
    have h2 := le_abs_self (u m - C)
    nlinarith [hKs]
  have hev2 := hF2.eventually (gt_mem_nhds hlt)
  have hev : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) := Ioo_mem_nhdsLT one_pos
  obtain ⟨p, h1, h2, h3⟩ := (hF1.and (hev2.and hev)).exists
  exact ⟨p, h3.1, h3.2, lt_of_le_of_lt h1 h2⟩

open RobustMeanCov.OnePoint in
theorem rmc_ops (u : ℝ → ℝ) (hu : Differentiable ℝ u)
    (hu' : Differentiable ℝ (deriv u)) (L : ℝ) (hL : ∀ t, L ≤ deriv (deriv u) t)
    (htend : ∀ m s : ℝ, 0 ≤ s →
      Tendsto (twoPointValue u m s) (𝓝[<] (1 : ℝ)) (𝓝 (u m + L * s ^ 2 / 2)) ∨
      Tendsto (twoPointValue u m s) (𝓝[>] (0 : ℝ)) (𝓝 (u m + L * s ^ 2 / 2))) :
    OnePointSupport u := by
  intro m s hs
  refine ⟨L / 2, deriv u m - L * m, u m - deriv u m * m + L * m ^ 2 / 2, ?_, ?_, ?_⟩
  · intro y
    have := rmc_global_lower u hu hu' L hL m y
    nlinarith [this]
  · ring
  · have e : L / 2 * (m ^ 2 + s ^ 2) + (deriv u m - L * m) * m
        + (u m - deriv u m * m + L * m ^ 2 / 2) = u m + L * s ^ 2 / 2 := by ring
    rw [e]
    exact (htend m s hs).symm

open RobustMeanCov.OnePoint in
theorem rmc_reflect_tendsto (u : ℝ → ℝ) (m s ℓ : ℝ)
    (h : Tendsto (twoPointValue (fun y => u (-y)) (-m) s) (𝓝[<] (1 : ℝ)) (𝓝 ℓ)) :
    Tendsto (twoPointValue u m s) (𝓝[>] (0 : ℝ)) (𝓝 ℓ) := by
  have hf : Tendsto (fun p : ℝ => 1 - p) (𝓝[>] (0 : ℝ)) (𝓝[<] (1 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have : Tendsto (fun p : ℝ => 1 - p) (𝓝 0) (𝓝 (1 - 0)) :=
        (continuous_const.sub continuous_id).tendsto 0
      simp only [sub_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with p hp
      simp only [Set.mem_Iio]
      have : (0 : ℝ) < p := hp
      linarith
  have := h.comp hf
  convert this using 1
  funext p
  simp only [Function.comp]
  exact rmc_refl_tpv u m s p

open MeasureTheory Filter Topology RobustMeanCov.OnePoint in
theorem solution (u : ℝ → ℝ)
    (hconc : ConcaveOn ℝ Set.univ u) (hu : Differentiable ℝ u)
    (hu' : Differentiable ℝ (deriv u))
    (hmono : Monotone (deriv (deriv u)) ∨ Antitone (deriv (deriv u))) :
    -- (a) `u'` convex: the limit of `u''` at `-∞`
    (ConvexOn ℝ Set.univ (deriv u) →
      (∀ L : ℝ, Tendsto (deriv (deriv u)) atBot (𝓝 L) →
        (∀ m s : ℝ, 0 ≤ s → ∀ ν ∈ RobustMeanCov.Shared.MeanVarClass m (s ^ 2), Integrable u ν) ∧
        (∀ m s : ℝ, 0 ≤ s →
          IsGLB {v : ℝ | ∃ ν ∈ RobustMeanCov.Shared.MeanVarClass m (s ^ 2), ∫ y, u y ∂ν = v}
            (u m + L * s ^ 2 / 2)) ∧
        OnePointSupport u) ∧
      (Tendsto (deriv (deriv u)) atBot atBot →
        ∀ m s : ℝ, 0 < s → ∀ C : ℝ,
          ∃ ν ∈ RobustMeanCov.Shared.MeanVarClass m (s ^ 2), Integrable u ν ∧ ∫ y, u y ∂ν < C)) ∧
    -- (b) `u'` concave: the limit of `u''` at `+∞`
    (ConcaveOn ℝ Set.univ (deriv u) →
      (∀ L : ℝ, Tendsto (deriv (deriv u)) atTop (𝓝 L) →
        (∀ m s : ℝ, 0 ≤ s → ∀ ν ∈ RobustMeanCov.Shared.MeanVarClass m (s ^ 2), Integrable u ν) ∧
        (∀ m s : ℝ, 0 ≤ s →
          IsGLB {v : ℝ | ∃ ν ∈ RobustMeanCov.Shared.MeanVarClass m (s ^ 2), ∫ y, u y ∂ν = v}
            (u m + L * s ^ 2 / 2)) ∧
        OnePointSupport u) ∧
      (Tendsto (deriv (deriv u)) atTop atBot →
        ∀ m s : ℝ, 0 < s → ∀ C : ℝ,
          ∃ ν ∈ RobustMeanCov.Shared.MeanVarClass m (s ^ 2), Integrable u ν ∧ ∫ y, u y ∂ν < C)) := by
  have hanti : Antitone (deriv u) :=
    antitoneOn_univ.1 (hconc.antitoneOn_deriv (fun x _ => (hu x)))
  have h0 : ∀ t, deriv (deriv u) t ≤ 0 := fun t => hanti.deriv_nonpos
  -- generic: from a lower bound L and a GLB-tendsto statement build the first triple
  have key : ∀ L : ℝ, (∀ t, L ≤ deriv (deriv u) t) →
      (∀ m s : ℝ, 0 ≤ s →
        Tendsto (twoPointValue u m s) (𝓝[<] (1 : ℝ)) (𝓝 (u m + L * s ^ 2 / 2)) ∨
        Tendsto (twoPointValue u m s) (𝓝[>] (0 : ℝ)) (𝓝 (u m + L * s ^ 2 / 2))) →
      ((∀ m s : ℝ, 0 ≤ s → ∀ ν ∈ RobustMeanCov.Shared.MeanVarClass m (s ^ 2), Integrable u ν) ∧
        (∀ m s : ℝ, 0 ≤ s →
          IsGLB {v : ℝ | ∃ ν ∈ RobustMeanCov.Shared.MeanVarClass m (s ^ 2), ∫ y, u y ∂ν = v}
            (u m + L * s ^ 2 / 2)) ∧
        OnePointSupport u) := by
    intro L hL htend
    refine ⟨fun m s _ ν hν => (rmc_core_L u hu hu' L hL h0 m s ν hν).1, ?_,
      rmc_ops u hu hu' L hL htend⟩
    intro m s hs
    constructor
    · rintro v ⟨ν, hν, rfl⟩
      exact (rmc_core_L u hu hu' L hL h0 m s ν hν).2
    · intro c hc
      have hev0 : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) := Ioo_mem_nhdsLT one_pos
      have hev1 : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT one_pos
      have hval : ∀ p : ℝ, 0 < p → p < 1 → c ≤ twoPointValue u m s p := by
        intro p hp0 hp1
        obtain ⟨ν, hν, hν2⟩ := rmc_two_point m s p hp0 hp1
        have h2 := (hν2 u hu.continuous)
        have := hc ⟨ν, hν, h2.2⟩
        simp only [twoPointValue]
        linarith [h2.2]
      rcases htend m s hs with h | h
      · refine ge_of_tendsto h ?_
        filter_upwards [hev0] with p hp
        exact hval p hp.1 hp.2
      · refine ge_of_tendsto h ?_
        filter_upwards [hev1] with p hp
        exact hval p hp.1 hp.2
  refine ⟨fun hconv => ⟨fun L hlim => ?_, fun hlim m s hs C => ?_⟩,
    fun hconv => ⟨fun L hlim => ?_, fun hlim m s hs C => ?_⟩⟩
  · -- (a) finite limit
    have hm : Monotone (deriv (deriv u)) :=
      monotoneOn_univ.1 (hconv.monotoneOn_deriv (fun x _ => hu' x))
    have hL : ∀ t, L ≤ deriv (deriv u) t := fun t => hm.le_of_tendsto hlim t
    exact key L hL (fun m s hs => Or.inl (rmc_coreA u hu hu' L hL h0 hlim m s hs))
  · -- (a) divergent limit
    obtain ⟨p, hp0, hp1, hpC⟩ := rmc_coreB u hu hu' hlim m s hs C
    obtain ⟨ν, hν, hν2⟩ := rmc_two_point m s p hp0 hp1
    have h2 := hν2 u hu.continuous
    refine ⟨ν, hν, h2.1, ?_⟩
    rw [h2.2]
    exact hpC
  · -- (b) finite limit
    have hm : Antitone (deriv (deriv u)) :=
      antitoneOn_univ.1 (hconv.antitoneOn_deriv (fun x _ => hu' x))
    have hL : ∀ t, L ≤ deriv (deriv u) t := fun t => hm.le_of_tendsto hlim t
    obtain ⟨hv, hv1, hv2, hv3⟩ := rmc_refl u hu hu'
    refine key L hL (fun m s hs => Or.inr ?_)
    have hlimv : Tendsto (deriv (deriv (fun y => u (-y)))) atBot (𝓝 L) := by
      rw [hv3]
      exact hlim.comp tendsto_neg_atBot_atTop
    have h0v : ∀ t, deriv (deriv (fun y => u (-y))) t ≤ 0 := by
      intro t; rw [hv3]; exact h0 (-t)
    have hLv : ∀ t, L ≤ deriv (deriv (fun y => u (-y))) t := by
      intro t; rw [hv3]; exact hL (-t)
    have := rmc_coreA (fun y => u (-y)) hv hv2 L hLv h0v hlimv (-m) s hs
    simp only [neg_neg] at this
    exact rmc_reflect_tendsto u m s _ this
  · -- (b) divergent limit
    obtain ⟨hv, hv1, hv2, hv3⟩ := rmc_refl u hu hu'
    have hlimv : Tendsto (deriv (deriv (fun y => u (-y)))) atBot atBot := by
      rw [hv3]
      exact hlim.comp tendsto_neg_atBot_atTop
    obtain ⟨p, hp0, hp1, hpC⟩ := rmc_coreB (fun y => u (-y)) hv hv2 hlimv (-m) s hs C
    obtain ⟨ν, hν, hν2⟩ := rmc_two_point m s (1 - p) (by linarith) (by linarith)
    have h2 := hν2 u hu.continuous
    refine ⟨ν, hν, h2.1, ?_⟩
    rw [h2.2]
    have h3 := rmc_refl_tpv u m s (1 - p)
    have e : 1 - (1 - p) = p := by ring
    rw [e] at h3
    have h4 : twoPointValue u m s (1 - p) < C := by rw [h3]; exact hpC
    exact h4
