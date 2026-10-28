-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P19.weighted_explicit_optimizers
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T09:05:50.212686+00:00
-- url     : https://prove2.me/submissions/46ac1ba1-4b06-4409-abbb-2aff112c0286

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

theorem WEO_eval {k : ℕ} {p : Polynomial ℝ} (hd : p.natDegree ≤ k) (hc : p.coeff 0 = 0) (x : ℝ) :
    p.eval x = ∑ j ∈ Finset.range k, p.coeff (j+1) * x^(j+1) := by
  rw [Polynomial.eval_eq_sum_range' (n := k+1) (by omega), Finset.sum_range_succ']
  simp [hc]

theorem WEO_deval {k : ℕ} (hk : 1 ≤ k) {p : Polynomial ℝ} (hd : p.natDegree ≤ k) (x : ℝ) :
    p.derivative.eval x = ∑ j ∈ Finset.range k, p.coeff (j+1) * ((j:ℝ)+1) * x^j := by
  have h1 := Polynomial.natDegree_derivative_le p
  rw [Polynomial.eval_eq_sum_range' (n := k) (by omega)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.coeff_derivative]

theorem WEO_mono (beta : ℝ) (h1 : beta < 3/2) (j : ℕ) :
    IntegrableOn (fun x : ℝ => Real.rpow x (-beta) * x^(j+1)) (Set.Ioc 0 1) ∧
    ∫ x in Set.Ioc (0:ℝ) 1, Real.rpow x (-beta) * x^(j+1) = 1/((j:ℝ)+2-beta) := by
  have hr : -1 < (j:ℝ) + 1 - beta := by have : (0:ℝ) ≤ j := Nat.cast_nonneg j; linarith
  have heq : Set.EqOn (fun x : ℝ => x ^ ((j:ℝ) + 1 - beta))
      (fun x : ℝ => Real.rpow x (-beta) * x^(j+1)) (Set.Ioc 0 1) := by
    intro x hx
    simp only [Real.rpow_eq_pow]
    rw [show (j:ℝ) + 1 - beta = -beta + ((j+1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_add hx.1, Real.rpow_natCast]
  refine ⟨((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) hr).1).congr_fun heq
    measurableSet_Ioc, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioc heq, ← intervalIntegral.integral_of_le zero_le_one,
    integral_rpow (Or.inl hr)]
  rw [Real.zero_rpow (by linarith), Real.one_rpow]
  congr 1 <;> ring

theorem WEO_sqrtint (beta : ℝ) (h1 : beta < 3/2) :
    IntegrableOn (fun x : ℝ => Real.rpow x (-beta) * Real.sqrt x) (Set.Ioc 0 1) := by
  have hr : -1 < -beta + 1/2 := by linarith
  have heq : Set.EqOn (fun x : ℝ => x ^ (-beta + 1/2))
      (fun x : ℝ => Real.rpow x (-beta) * Real.sqrt x) (Set.Ioc 0 1) := by
    intro x hx
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_add hx.1, Real.sqrt_eq_rpow]
  exact ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) hr).1).congr_fun heq
    measurableSet_Ioc

theorem WEO_err (beta : ℝ) (h0 : 0 ≤ beta) (h1 : beta < 3/2) (k : ℕ) (p : Polynomial ℝ)
    (hd : p.natDegree ≤ k) (hc : p.coeff 0 = 0) :
    weightedError beta h0 h1 p =
      (∫ x in Set.Ioc (0:ℝ) 1, Real.rpow x (-beta) * Real.sqrt x) - weightedScore k beta p := by
  unfold weightedError weightedScore
  have hfun : (fun x : ℝ => Real.rpow x (-beta) * (Real.sqrt x - p.eval x)) =
      fun x => Real.rpow x (-beta) * Real.sqrt x -
        ∑ j ∈ Finset.range k, p.coeff (j+1) * (Real.rpow x (-beta) * x^(j+1)) := by
    funext x
    rw [WEO_eval hd hc, mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hfun, integral_sub (WEO_sqrtint beta h1)
    (integrable_finsetSum _ fun j _ => (WEO_mono beta h1 j).1.const_mul _),
    integral_finsetSum _ fun j _ => (WEO_mono beta h1 j).1.const_mul _]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, (WEO_mono beta h1 j).2]
  ring

theorem WEO_deriv {k : ℕ} {g : Polynomial ℝ} (hg : minorantFeasible k g) :
    1/2 ≤ g.derivative.eval 1 := by
  by_contra hlt'
  have hlt := not_le.1 hlt'
  have hd : HasDerivAt (fun x => g.eval x - Real.sqrt x)
      (g.derivative.eval 1 - 1 / (2 * Real.sqrt 1)) 1 :=
    (g.hasDerivAt 1).sub (Real.hasDerivAt_sqrt one_ne_zero)
  rw [Real.sqrt_one] at hd
  have ht := (hasDerivAt_iff_tendsto_slope.1 hd).mono_left
    (nhdsWithin_mono _ fun y (hy : y ∈ Set.Iio (1:ℝ)) => ne_of_lt hy)
  have hev := ht.eventually (gt_mem_nhds (show g.derivative.eval 1 - 1 / (2*1) < 0 by linarith))
  obtain ⟨y, hy1, hy2⟩ := (hev.and (Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num))).exists
  rw [slope_def_field] at hy1
  have h1 : g.eval 1 - Real.sqrt 1 = 0 := by rw [hg.2.2.1, Real.sqrt_one]; ring
  rw [h1, sub_zero] at hy1
  have h2 : g.eval y - Real.sqrt y ≤ 0 := by
    have := hg.2.2.2 y ⟨hy2.1.le, hy2.2.le⟩; linarith
  have := div_nonneg_of_nonpos h2 (by linarith [hy2.2] : y - 1 ≤ 0)
  linarith

theorem WEO_sq {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ x = t^2 ∧ Real.sqrt x = t := by
  refine ⟨Real.sqrt x, Real.sqrt_nonneg x, ?_, (Real.sq_sqrt hx.1).symm, rfl⟩
  have := Real.sqrt_le_sqrt hx.2
  rwa [Real.sqrt_one] at this

theorem WEO_s3 : Real.sqrt (1/3) = Real.sqrt 3 / 3 := by
  rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by positivity)]
  nlinarith [Real.mul_self_sqrt (show (0:ℝ) ≤ 3 by norm_num)]

theorem WEO_s2 : Real.sqrt (1/2) = Real.sqrt 2 / 2 := by
  rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by positivity)]
  nlinarith [Real.mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num)]

theorem WEO_s4 : Real.sqrt (1/4) = 1/2 := by
  rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by positivity)]
  norm_num

theorem WEO_X_feas : minorantFeasible 1 (Polynomial.X : Polynomial ℝ) := by
  refine ⟨Polynomial.natDegree_X_le, by simp, by simp, fun x hx => ?_⟩
  obtain ⟨t, ht0, ht1, rfl, hs⟩ := WEO_sq hx
  rw [hs, Polynomial.eval_X]
  nlinarith

theorem WEO_k1 (beta : ℝ) (h0 : 0 ≤ beta) (h1 : beta < 3/2) :
    WeightedOptimizer 1 beta Polynomial.X := by
  refine ⟨h0, h1, WEO_X_feas, fun g hg => ?_⟩
  rw [WEO_err beta h0 h1 1 _ hg.1 hg.2.1, WEO_err beta h0 h1 1 _ WEO_X_feas.1 WEO_X_feas.2.1]
  have e1 := hg.2.2.1
  rw [WEO_eval hg.1 hg.2.1] at e1
  simp [weightedScore] at e1 ⊢
  rw [e1]
  linarith [one_div (2 - beta)]

theorem WEO_h2_feas :
    minorantFeasible 2 ((3/2:ℝ) • Polynomial.X-(1/2:ℝ) • Polynomial.X^2) := by
  refine ⟨by compute_degree!, by simp, by simp; norm_num, fun x hx => ?_⟩
  obtain ⟨t, ht0, ht1, rfl, hs⟩ := WEO_sq hx
  rw [hs]
  simp only [Polynomial.eval_sub, Polynomial.eval_smul, Polynomial.eval_X, Polynomial.eval_pow,
    smul_eq_mul]
  nlinarith [mul_nonneg (mul_nonneg ht0 (sq_nonneg (1-t))) (by linarith : (0:ℝ) ≤ t+2)]

theorem WEO_k2 (beta : ℝ) (h0 : 0 ≤ beta) (h1 : beta < 3/2) :
    WeightedOptimizer 2 beta ((3/2:ℝ) • Polynomial.X-(1/2:ℝ) • Polynomial.X^2) := by
  refine ⟨h0, h1, WEO_h2_feas, fun g hg => ?_⟩
  rw [WEO_err beta h0 h1 2 _ hg.1 hg.2.1, WEO_err beta h0 h1 2 _ WEO_h2_feas.1 WEO_h2_feas.2.1]
  have e1 := hg.2.2.1
  rw [WEO_eval hg.1 hg.2.1] at e1
  have e3 := WEO_deriv hg
  rw [WEO_deval (by norm_num) hg.1] at e3
  simp [Finset.sum_range_succ] at e1 e3
  have hb : g.coeff 2 = 1 - g.coeff 1 := by linarith
  have hu : 0 < 2 - beta := by linarith
  have hv : 0 < 3 - beta := by linarith
  simp [weightedScore, Finset.sum_range_succ, Polynomial.coeff_X, Polynomial.coeff_X_pow]
  rw [hb]
  norm_num
  have key : (3/2)/(2-beta) + (-1/2)/(3-beta) - (g.coeff 1/(2-beta) + (1-g.coeff 1)/(3-beta))
      = (3/2 - g.coeff 1)/((2-beta)*(3-beta)) := by
    field_simp; ring
  have : 0 ≤ (3/2 - g.coeff 1)/((2-beta)*(3-beta)) := div_nonneg (by linarith) (by positivity)
  linarith

theorem WEO_h3_feas : minorantFeasible 3 ((1/4+3*Real.sqrt 3/2) • Polynomial.X -
       (3/2+3*Real.sqrt 3/2) • Polynomial.X^2 + (9/4:ℝ) • Polynomial.X^3) := by
  refine ⟨by compute_degree!, by simp, by simp; ring, fun x hx => ?_⟩
  obtain ⟨t, ht0, ht1, rfl, hs⟩ := WEO_sq hx
  rw [hs]
  simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_smul, Polynomial.eval_X,
    Polynomial.eval_pow, smul_eq_mul]
  set s := Real.sqrt 3 with hsdef
  have hs3 : s^2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg 3
  have fac : t - ((1/4+3*s/2) * t^2 - (3/2+3*s/2) * (t^2)^2 + 9/4 * (t^2)^3) =
      t * (1-t) * (t - s/3)^2 * (9/4*t^2 + (3/2*s + 9/4)*t + 3) := by
    linear_combination (-1/3*t + 1/12*t^2 + t^3 - 3/4*t^4 - 1/6*s*t^2 + 1/6*s*t^3) * hs3
  have : 0 ≤ t * (1-t) * (t - s/3)^2 * (9/4*t^2 + (3/2*s + 9/4)*t + 3) := by
    have : 0 ≤ 1 - t := by linarith
    positivity
  linarith

theorem WEO_h4_feas : minorantFeasible 4 ((185/54:ℝ) • Polynomial.X-(137/18:ℝ) • Polynomial.X^2 +
       (76/9:ℝ) • Polynomial.X^3-(88/27:ℝ) • Polynomial.X^4) := by
  refine ⟨by compute_degree!, by simp, by simp; norm_num, fun x hx => ?_⟩
  obtain ⟨t, ht0, ht1, rfl, hs⟩ := WEO_sq hx
  rw [hs]
  simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_smul, Polynomial.eval_X,
    Polynomial.eval_pow, smul_eq_mul]
  have fac : 54 * (t - (185/54 * t^2 - 137/18 * (t^2)^2 + 76/9 * (t^2)^3 - 88/27 * (t^2)^4)) =
      t * ((2*t-1)*(t-1))^2 * (44*t^3 + 132*t^2 + 139*t + 54) := by ring
  have : 0 ≤ t * ((2*t-1)*(t-1))^2 * (44*t^3 + 132*t^2 + 139*t + 54) := by positivity
  linarith

theorem WEO_h30_feas : minorantFeasible 3 ((1+Real.sqrt 2) • Polynomial.X -
       (4-Real.sqrt 2) • Polynomial.X^2 + (4-2*Real.sqrt 2) • Polynomial.X^3) := by
  refine ⟨by compute_degree!, by simp, by simp; ring, fun x hx => ?_⟩
  obtain ⟨t, ht0, ht1, rfl, hs⟩ := WEO_sq hx
  rw [hs]
  simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_smul, Polynomial.eval_X,
    Polynomial.eval_pow, smul_eq_mul]
  set s := Real.sqrt 2 with hsdef
  have hs2 : s^2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg 2
  have hs1 : s ≤ 2 := by nlinarith
  have fac : t - ((1+s) * t^2 - (4-s) * (t^2)^2 + (4-2*s) * (t^2)^3) =
      t * (1-t) * (t - s/2)^2 * ((4-2*s)*t^2 + 2*s*t + 2) := by
    linear_combination (-1/2*t + 1/2*t^2 + t^3 - 3*t^4 + 2*t^5 - 1/2*s*t^2 + s*t^3
      - 1/2*s*t^4) * hs2
  have : 0 ≤ t * (1-t) * (t - s/2)^2 * ((4-2*s)*t^2 + 2*s*t + 2) := by
    have : 0 ≤ 1 - t := by linarith
    have : 0 ≤ 4 - 2*s := by linarith
    positivity
  linarith

theorem WEO_h3 : WeightedOptimizer 3 1 ((1/4+3*Real.sqrt 3/2) • Polynomial.X -
       (3/2+3*Real.sqrt 3/2) • Polynomial.X^2 + (9/4:ℝ) • Polynomial.X^3) := by
  refine ⟨by norm_num, by norm_num, WEO_h3_feas, fun g hg => ?_⟩
  rw [WEO_err 1 _ _ 3 _ hg.1 hg.2.1, WEO_err 1 _ _ 3 _ WEO_h3_feas.1 WEO_h3_feas.2.1]
  have e1 := hg.2.2.1
  have e2 := hg.2.2.2 (1/3) ⟨by norm_num, by norm_num⟩
  rw [WEO_eval hg.1 hg.2.1] at e1 e2
  rw [WEO_s3] at e2
  simp [Finset.sum_range_succ] at e1 e2
  simp [weightedScore, Finset.sum_range_succ, Polynomial.coeff_X, Polynomial.coeff_X_pow]
  norm_num
  linarith

theorem WEO_h4 : WeightedOptimizer 4 1 ((185/54:ℝ) • Polynomial.X-(137/18:ℝ) • Polynomial.X^2 +
       (76/9:ℝ) • Polynomial.X^3-(88/27:ℝ) • Polynomial.X^4) := by
  refine ⟨by norm_num, by norm_num, WEO_h4_feas, fun g hg => ?_⟩
  rw [WEO_err 1 _ _ 4 _ hg.1 hg.2.1, WEO_err 1 _ _ 4 _ WEO_h4_feas.1 WEO_h4_feas.2.1]
  have e1 := hg.2.2.1
  have e2 := hg.2.2.2 (1/4) ⟨by norm_num, by norm_num⟩
  have e3 := WEO_deriv hg
  rw [WEO_eval hg.1 hg.2.1] at e1 e2
  rw [WEO_deval (by norm_num) hg.1] at e3
  rw [WEO_s4] at e2
  simp [Finset.sum_range_succ] at e1 e2 e3
  simp [weightedScore, Finset.sum_range_succ, Polynomial.coeff_X, Polynomial.coeff_X_pow]
  norm_num at e3 ⊢
  linarith

theorem WEO_h30 : WeightedOptimizer 3 0 ((1+Real.sqrt 2) • Polynomial.X -
       (4-Real.sqrt 2) • Polynomial.X^2 + (4-2*Real.sqrt 2) • Polynomial.X^3) := by
  refine ⟨by norm_num, by norm_num, WEO_h30_feas, fun g hg => ?_⟩
  rw [WEO_err 0 _ _ 3 _ hg.1 hg.2.1, WEO_err 0 _ _ 3 _ WEO_h30_feas.1 WEO_h30_feas.2.1]
  have e1 := hg.2.2.1
  have e2 := hg.2.2.2 (1/2) ⟨by norm_num, by norm_num⟩
  rw [WEO_eval hg.1 hg.2.1] at e1 e2
  rw [WEO_s2] at e2
  simp [Finset.sum_range_succ] at e1 e2
  simp [weightedScore, Finset.sum_range_succ, Polynomial.coeff_X, Polynomial.coeff_X_pow]
  norm_num
  linarith

theorem WEO_e3 : ((1/4+3*Real.sqrt 3/2) • Polynomial.X -
       (3/2+3*Real.sqrt 3/2) • Polynomial.X^2 + (9/4:ℝ) • Polynomial.X^3 : Polynomial ℝ).eval (1/3)
       = Real.sqrt (1/3) := by
  rw [WEO_s3]; simp; ring

theorem WEO_e4 : ((185/54:ℝ) • Polynomial.X-(137/18:ℝ) • Polynomial.X^2 +
       (76/9:ℝ) • Polynomial.X^3-(88/27:ℝ) • Polynomial.X^4 : Polynomial ℝ).eval (1/4)
       = Real.sqrt (1/4) := by
  rw [WEO_s4]; simp; norm_num

theorem WEO_d4 : ((185/54:ℝ) • Polynomial.X-(137/18:ℝ) • Polynomial.X^2 +
       (76/9:ℝ) • Polynomial.X^3-(88/27:ℝ) • Polynomial.X^4 : Polynomial ℝ).derivative.eval 1
       = 1/2 := by
  simp; norm_num

theorem WEO_e30 : ((1+Real.sqrt 2) • Polynomial.X -
       (4-Real.sqrt 2) • Polynomial.X^2 + (4-2*Real.sqrt 2) • Polynomial.X^3 : Polynomial ℝ).eval
       (1/2) = Real.sqrt (1/2) := by
  rw [WEO_s2]; simp; ring

end QAlgorithms.Papers.Independent.Information100.P19

open QAlgorithms.Papers.Independent.Information100.P19 in
theorem solution  :
    (∀ beta : ℝ, 0≤beta → beta<3/2 →
      WeightedOptimizer 1 beta Polynomial.X ∧
      WeightedOptimizer 2 beta ((3/2:ℝ) • Polynomial.X-(1/2:ℝ) • Polynomial.X^2)) ∧
    (let h3 : Polynomial ℝ :=
       (1/4+3*Real.sqrt 3/2) • Polynomial.X -
       (3/2+3*Real.sqrt 3/2) • Polynomial.X^2 + (9/4:ℝ) • Polynomial.X^3
     let h4 : Polynomial ℝ := (185/54:ℝ) • Polynomial.X-(137/18:ℝ) • Polynomial.X^2 +
       (76/9:ℝ) • Polynomial.X^3-(88/27:ℝ) • Polynomial.X^4
     let h30 : Polynomial ℝ := (1+Real.sqrt 2) • Polynomial.X -
       (4-Real.sqrt 2) • Polynomial.X^2 + (4-2*Real.sqrt 2) • Polynomial.X^3
     WeightedOptimizer 3 1 h3 ∧ WeightedOptimizer 4 1 h4 ∧ WeightedOptimizer 3 0 h30 ∧
       h3.eval (1/3)=Real.sqrt (1/3) ∧ h4.eval (1/4)=Real.sqrt (1/4) ∧
       h4.derivative.eval 1=1/2 ∧ h30.eval (1/2)=Real.sqrt (1/2)) := by
  refine ⟨fun beta h0 h1 => ⟨WEO_k1 beta h0 h1, WEO_k2 beta h0 h1⟩, ?_⟩
  intro h3 h4 h30
  exact ⟨WEO_h3, WEO_h4, WEO_h30, WEO_e3, WEO_e4, WEO_d4, WEO_e30⟩

end

