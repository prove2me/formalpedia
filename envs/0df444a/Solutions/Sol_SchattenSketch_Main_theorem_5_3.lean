-- Prove2me | solution 1 for SchattenSketch.Main.theorem_5_3
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-23T06:17:25.664169+00:00
-- url     : https://prove2.me/submissions/369534d4-65a3-43fe-940c-e773a658e81f

import Mathlib

section PartB
open Complex Real MeasureTheory

lemma int_coeff_integral (n : ℤ) :
    ∫ x in (-(π/2))..(π/2), cexp (-(2 * I * n * x)) * (Real.cos x : ℂ)
      = (-1 : ℂ) ^ n * 2 / (1 - 4 * (n:ℂ) ^ 2) := by
  have hα : (1 - 2 * (n:ℂ)) ≠ 0 := by
    intro h
    have : ((1 - 2 * n : ℤ) : ℂ) = 0 := by push_cast; exact h
    have := Int.cast_eq_zero.mp this
    omega
  have hβ : (1 + 2 * (n:ℂ)) ≠ 0 := by
    intro h
    have : ((1 + 2 * n : ℤ) : ℂ) = 0 := by push_cast; exact h
    have := Int.cast_eq_zero.mp this
    omega
  set F : ℝ → ℂ := fun x => (cexp (I * (1 - 2 * n) * x) / (I * (1 - 2 * n))
      - cexp ((-(I * (1 + 2 * n))) * x) / (I * (1 + 2 * n))) / 2 with hF
  have hd : ∀ x : ℝ, HasDerivAt F (cexp (-(2 * I * n * x)) * (Real.cos x : ℂ)) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => I * (1 - 2 * (n:ℂ)) * (x:ℂ)) (I * (1 - 2 * n)) x := by
      simpa using (hasDerivAt_id (x:ℂ)).const_mul (I * (1 - 2 * (n:ℂ))) |>.comp_ofReal
    have h2 : HasDerivAt (fun x : ℝ => (-(I * (1 + 2 * (n:ℂ)))) * (x:ℂ)) (-(I * (1 + 2 * n))) x := by
      simpa using ((hasDerivAt_id (x:ℂ)).const_mul (-(I * (1 + 2 * (n:ℂ)))) |>.comp_ofReal)
    have h3 := ((h1.cexp.div_const (I * (1 - 2 * n))).sub (h2.cexp.div_const (I * (1 + 2 * n)))).div_const 2
    refine h3.congr_deriv ?_
    rw [Complex.ofReal_cos, Complex.cos]
    field_simp
    rw [sub_neg_eq_add, mul_add (cexp (-(I * 2 * (n:ℂ) * (x:ℂ)))) (cexp (I * (x:ℂ))), ← Complex.exp_add, ← Complex.exp_add]
    congr 1 <;> congr 1 <;> ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)]
  · have h0 : cexp (↑π / 2 * I) = I := Complex.exp_pi_div_two_mul_I
    have hn : ∀ m : ℤ, cexp ((m:ℂ) * (↑π * I)) = (-1 : ℂ) ^ m := by
      intro m; rw [Complex.exp_int_mul, Complex.exp_pi_mul_I]
    have hs : ((-1 : ℂ) ^ n)⁻¹ = (-1 : ℂ) ^ n := by
      rcases Int.even_or_odd n with h | h <;> simp [h.neg_one_zpow]
    have t1 : cexp (I * (1 - 2 * n) * ((π/2 : ℝ) : ℂ)) = I * (-1 : ℂ) ^ n := by
      rw [show I * (1 - 2 * (n:ℂ)) * ((π/2 : ℝ) : ℂ) = ↑π / 2 * I + ((-n : ℤ) : ℂ) * (↑π * I) by
        push_cast; ring, Complex.exp_add, h0, hn, zpow_neg, hs]
    have t2 : cexp (I * (1 - 2 * n) * ((-(π/2) : ℝ) : ℂ)) = -(I * (-1 : ℂ) ^ n) := by
      rw [show I * (1 - 2 * (n:ℂ)) * ((-(π/2) : ℝ) : ℂ) = -(↑π / 2 * I) + ((n : ℤ) : ℂ) * (↑π * I) by
        push_cast; ring, Complex.exp_add, Complex.exp_neg, h0, hn, Complex.inv_I]
      ring
    have t3 : cexp ((-(I * (1 + 2 * n))) * ((π/2 : ℝ) : ℂ)) = -(I * (-1 : ℂ) ^ n) := by
      rw [show (-(I * (1 + 2 * (n:ℂ)))) * ((π/2 : ℝ) : ℂ) = -(↑π / 2 * I) + ((-n : ℤ) : ℂ) * (↑π * I) by
        push_cast; ring, Complex.exp_add, Complex.exp_neg, h0, hn, Complex.inv_I, zpow_neg, hs]
      ring
    have t4 : cexp ((-(I * (1 + 2 * n))) * ((-(π/2) : ℝ) : ℂ)) = I * (-1 : ℂ) ^ n := by
      rw [show (-(I * (1 + 2 * (n:ℂ)))) * ((-(π/2) : ℝ) : ℂ) = ↑π / 2 * I + ((n : ℤ) : ℂ) * (↑π * I) by
        push_cast; ring, Complex.exp_add, h0, hn]
    simp only [hF]
    rw [t1, t2, t3, t4]
    have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
    field_simp
    rw [show (1 - (n:ℂ)^2*4) = (1 - 2*n)*(1 + 2*n) by ring]
    field_simp
    ring
  · apply Continuous.intervalIntegrable
    fun_prop

instance instFactPi : Fact (0 < π) := ⟨Real.pi_pos⟩

noncomputable def absCosC : C(AddCircle π, ℂ) :=
  ⟨(show Function.Periodic (fun x : ℝ => ((|Real.cos x| : ℝ) : ℂ)) π from fun x => by
      simp [Real.cos_add_pi]).lift,
    continuous_coinduced_dom.mpr
      (by have : Continuous (fun x : ℝ => ((|Real.cos x| : ℝ) : ℂ)) := by fun_prop
          exact this)⟩

noncomputable def cc (z : ℤ) : ℝ := 2 / π * (-1 : ℝ) ^ z / (1 - 4 * (z : ℝ) ^ 2)

lemma absCosC_coeff (n : ℤ) : fourierCoeff absCosC n = ((cc n : ℝ) : ℂ) := by
  rw [fourierCoeff_eq_intervalIntegral _ n (-(π/2))]
  have h : -(π/2) + π = π/2 := by ring
  rw [h]
  have : ∫ x in (-(π/2))..(π/2), fourier (-n) (x : AddCircle π) • absCosC (x : AddCircle π)
      = ∫ x in (-(π/2))..(π/2), cexp (-(2 * I * n * x)) * (Real.cos x : ℂ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hx
    simp only [absCosC, ContinuousMap.coe_mk, Function.Periodic.lift_coe, smul_eq_mul]
    rw [abs_of_nonneg (Real.cos_nonneg_of_mem_Icc hx), fourier_coe_apply]
    congr 2
    push_cast
    field_simp
  rw [this, int_coeff_integral]
  simp only [cc, Complex.real_smul]
  push_cast
  have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

lemma cc_neg (z : ℤ) : cc (-z) = cc z := by
  unfold cc
  have : (-1 : ℝ) ^ (-z) = (-1) ^ z := by
    rw [zpow_neg]
    rcases Int.even_or_odd z with h | h <;> simp [h.neg_one_zpow]
  rw [this]; push_cast; ring_nf

lemma cc_bound (z : ℤ) : |cc z| ≤ 4 / π / ((|(z : ℝ)|) + 1) ^ 2 := by
  have hd : (|(z : ℝ)| + 1) ^ 2 ≤ 2 * |1 - 4 * (z : ℝ) ^ 2| := by
    rcases eq_or_ne z 0 with h | h
    · subst h; norm_num
    · have h1 : (1 : ℝ) ≤ |(z : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs h
      have h2 : (z : ℝ) ^ 2 = |(z : ℝ)| ^ 2 := (sq_abs _).symm
      have h3 : |1 - 4 * |(z : ℝ)| ^ 2| = 4 * |(z : ℝ)| ^ 2 - 1 := by
        rw [abs_of_nonpos (by nlinarith)]; ring
      rw [h2, h3]
      nlinarith
  unfold cc
  rw [abs_div, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, mul_one, abs_div, abs_two,
    abs_of_pos Real.pi_pos]
  have hp := Real.pi_pos
  have hd0 : 0 < |1 - 4 * (z : ℝ) ^ 2| := by
    have := lt_of_lt_of_le (by positivity : (0:ℝ) < (|(z:ℝ)| + 1) ^ 2) hd
    linarith
  rw [div_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hd hp.le]

lemma abs_cos_hasSum_int (x : ℝ) :
    HasSum (fun z : ℤ => cc z * Real.cos (2 * z * x)) |Real.cos x| := by
  have hs : Summable (fourierCoeff absCosC) := by
    have hb : ∀ m : ℕ, |cc m| ≤ 4 / π * (1 / (((m + 1 : ℕ) : ℝ)) ^ 2) := by
      intro m
      have h := cc_bound m
      have e : |(((m : ℤ)) : ℝ)| = m := by push_cast; exact abs_of_nonneg (by positivity)
      rw [e] at h
      push_cast
      rw [div_eq_mul_one_div] at h
      exact h
    have hb2 : ∀ m : ℕ, |cc (-(m + 1 : ℤ))| ≤ 4 / π * (1 / (((m + 1 : ℕ) : ℝ)) ^ 2) := by
      intro m
      have h := cc_bound (-(m + 1 : ℤ))
      have e : |(((-(m + 1 : ℤ)) : ℤ) : ℝ)| = m + 1 := by
        push_cast; rw [abs_neg]; exact abs_of_nonneg (by positivity)
      rw [e, div_eq_mul_one_div] at h
      refine h.trans ?_
      push_cast
      have : (1:ℝ) / ((m + 1) + 1) ^ 2 ≤ 1 / ((m : ℝ) + 1) ^ 2 := by
        gcongr; linarith
      have hp : 0 < 4 / π := by positivity
      exact mul_le_mul_of_nonneg_left this hp.le
    have hg : Summable (fun m : ℕ => 4 / π * (1 / (((m + 1 : ℕ) : ℝ)) ^ 2)) :=
      ((summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)).mul_left _
    refine Summable.of_nat_of_neg_add_one ?_ ?_
    · refine Summable.of_norm_bounded hg (fun m => ?_)
      rw [absCosC_coeff, Complex.norm_real, Real.norm_eq_abs]; exact hb m
    · refine Summable.of_norm_bounded hg (fun m => ?_)
      rw [absCosC_coeff, Complex.norm_real, Real.norm_eq_abs]; exact hb2 m
  have h := has_pointwise_sum_fourier_series_of_summable hs (x : AddCircle π)
  have h2 := Complex.reCLM.hasSum h
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  convert h2 using 1
  · funext z
    rw [absCosC_coeff, fourier_coe_apply, smul_eq_mul]
    have : (2 * (π : ℂ) * I * z * x / π) = ((2 * z * x : ℝ) : ℂ) * I := by
      push_cast; field_simp
    rw [this]
    rw [Complex.reCLM_apply, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  · simp [absCosC]

lemma cc_neg' (n : ℕ) : cc (-(n + 1 : ℤ)) = cc ((n + 1 : ℕ) : ℤ) := by
  rw [← cc_neg]; push_cast; ring_nf

end PartB

section PartC
open Real

noncomputable def bb (n : ℕ) : ℝ := if n = 0 then cc 0 else 2 * cc n

lemma abs_cos_hasSum_nat (x : ℝ) :
    HasSum (fun n : ℕ => bb n * Real.cos (2 * n * x)) |Real.cos x| := by
  set h : ℤ → ℝ := fun z => cc z * Real.cos (2 * z * x) with hh
  have hint := abs_cos_hasSum_int x
  have hsum : Summable h := hint.summable
  have hA := (hsum.comp_injective Nat.cast_injective).hasSum
  have hneg : ∀ n : ℕ, h (-(n + 1 : ℤ)) = h ((n + 1 : ℕ) : ℤ) := by
    intro n
    simp only [hh]
    rw [cc_neg' n]
    have : (2 * ((-(n + 1 : ℤ) : ℤ) : ℝ) * x) = -(2 * (((n + 1 : ℕ) : ℤ) : ℝ) * x) := by
      push_cast; ring
    rw [this, Real.cos_neg]
  have hshift : HasSum (fun n : ℕ => h ((n + 1 : ℕ) : ℤ)) ((∑' n : ℕ, h (n : ℤ)) - h 0) := by
    have := (hasSum_nat_add_iff' 1).mpr hA
    simpa using this
  have hB' : HasSum (fun n : ℕ => h (-(n + 1 : ℤ))) ((∑' n : ℕ, h (n : ℤ)) - h 0) := by
    simpa only [hneg] using hshift
  have htot := hA.of_nat_of_neg_add_one hB'
  have hval := hint.unique htot
  have h0 : h 0 = cc 0 := by simp [hh]
  have hb : HasSum (fun n : ℕ => bb (n + 1) * Real.cos (2 * ((n + 1 : ℕ) : ℝ) * x))
      (2 * ((∑' n : ℕ, h (n : ℤ)) - h 0)) := by
    have := hshift.mul_left 2
    have e : (fun n : ℕ => bb (n + 1) * Real.cos (2 * ((n + 1 : ℕ) : ℝ) * x))
        = fun i : ℕ => 2 * h ((i + 1 : ℕ) : ℤ) := by
      funext n
      simp [bb, hh]
      ring
    rw [e]; exact this
  refine (hasSum_nat_add_iff' 1).mp ?_
  have e2 : |Real.cos x| - ∑ i ∈ Finset.range 1, bb i * Real.cos (2 * (i : ℝ) * x)
      = 2 * ((∑' n : ℕ, h (n : ℤ)) - h 0) := by
    have : ∑' (b : ℕ), (h ∘ Nat.cast) b = ∑' n : ℕ, h (n : ℤ) := rfl
    rw [Finset.sum_range_one]
    simp only [bb, if_true, Nat.cast_zero, mul_zero, zero_mul, Real.cos_zero, mul_one]
    rw [hval, this]
    linarith
  rw [e2]; exact hb

lemma tel_sum (a : ℝ) (ha : 0 < a) (N : ℕ) :
    ∑ i ∈ Finset.range N, 1 / (((i : ℝ) + a) * ((i : ℝ) + a + 1)) = 1 / a - 1 / ((N : ℝ) + a) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    have h1 : (0 : ℝ) < (N : ℝ) + a := by positivity
    field_simp
    ring

lemma bb_bound (m : ℕ) : |bb (m + 1)| ≤ 8 / π * (1 / (((m : ℝ) + 1) * ((m : ℝ) + 1 + 1))) := by
  have h := cc_bound ((m + 1 : ℕ) : ℤ)
  have e : |(((m + 1 : ℕ) : ℤ) : ℝ)| = (m : ℝ) + 1 := by
    push_cast; exact abs_of_nonneg (by positivity)
  rw [e] at h
  simp only [bb, Nat.add_one_ne_zero, if_false, abs_mul, abs_two]
  have hp := Real.pi_pos
  have hm : (0 : ℝ) ≤ m := by positivity
  have h2 : 1 / ((m : ℝ) + 1 + 1) ^ 2 ≤ 1 / (((m : ℝ) + 1) * ((m : ℝ) + 1 + 1)) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have h3 : 4 / π / ((m : ℝ) + 1 + 1) ^ 2 ≤ 4 / π * (1 / (((m : ℝ) + 1) * ((m : ℝ) + 1 + 1))) := by
    rw [div_eq_mul_one_div (4 / π)]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have : 8 / π = 2 * (4 / π) := by ring
  rw [this, mul_assoc]
  linarith

lemma abs_cos_tail (x : ℝ) (K : ℕ) :
    |(|Real.cos x|) - ∑ n ∈ Finset.range (K + 1), bb n * Real.cos (2 * n * x)| ≤ 8 / π / (K + 1) := by
  have hs := abs_cos_hasSum_nat x
  have hr := (hasSum_nat_add_iff' (K + 1)).mpr hs
  have hp := Real.pi_pos
  set G : ℕ → ℝ := fun n => 8 / π * (1 / (((n : ℝ) + ((K : ℝ) + 1)) * ((n : ℝ) + ((K : ℝ) + 1) + 1))) with hG
  have hpart : ∀ N, ∑ i ∈ Finset.range N, G i ≤ 8 / π / (K + 1) := by
    intro N
    have h := tel_sum ((K : ℝ) + 1) (by positivity) N
    have : ∑ i ∈ Finset.range N, G i = 8 / π * (1 / ((K : ℝ) + 1) - 1 / ((N : ℝ) + ((K : ℝ) + 1))) := by
      rw [← h, Finset.mul_sum]
    rw [this]
    have : 0 ≤ 1 / ((N : ℝ) + ((K : ℝ) + 1)) := by positivity
    rw [div_eq_mul_one_div (8 / π)]
    nlinarith [div_pos (by norm_num : (0:ℝ) < 8) hp]
  have hGnn : ∀ n, 0 ≤ G n := fun n => by simp only [hG]; positivity
  have hGs : Summable G := summable_of_sum_range_le hGnn hpart
  have hb := Real.tsum_le_of_sum_range_le hGnn hpart
  have := hr.norm_le_of_bounded hGs.hasSum (fun n => ?_)
  · rw [Real.norm_eq_abs] at this
    exact this.trans hb
  · rw [Real.norm_eq_abs, abs_mul]
    have h1 := bb_bound (n + K)
    have h2 : |Real.cos (2 * ((n + (K + 1) : ℕ) : ℝ) * x)| ≤ 1 := Real.abs_cos_le_one _
    simp only [hG]
    calc _ ≤ |bb (n + (K + 1))| * 1 := by gcongr
      _ ≤ _ := by
        rw [mul_one, show n + (K + 1) = n + K + 1 by ring]
        convert h1 using 4 <;> push_cast <;> ring

lemma bb_sum_le (K : ℕ) : ∑ n ∈ Finset.range (K + 1), |bb n| ≤ 4 := by
  have hp := Real.pi_pos
  have hp3 : (3 : ℝ) < π := Real.pi_gt_three
  have h0 : |bb 0| ≤ 1 := by
    simp only [bb, if_true, cc]
    rw [abs_div, abs_mul, abs_zpow]
    simp
    rw [abs_of_pos (by positivity), div_le_one hp]; linarith
  have key : ∀ N : ℕ, ∑ n ∈ Finset.range N, |bb (n + 1)| ≤ 8 / π := by
    intro N
    have h := tel_sum 1 one_pos N
    have : ∑ n ∈ Finset.range N, |bb (n + 1)| ≤ ∑ n ∈ Finset.range N,
        8 / π * (1 / (((n : ℝ) + 1) * ((n : ℝ) + 1 + 1))) :=
      Finset.sum_le_sum (fun n _ => bb_bound n)
    rw [← Finset.mul_sum, h] at this
    refine this.trans ?_
    have : 0 ≤ 1 / ((N : ℝ) + 1) := by positivity
    nlinarith [div_pos (by norm_num : (0:ℝ) < 8) hp]
  rw [Finset.sum_range_succ']
  have := key K
  have h8 : 8 / π ≤ 3 := by rw [div_le_iff₀ hp]; linarith
  linarith

end PartC

section PartF
open Real Polynomial

noncomputable def Tp : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 2 * X - 1
  | (k + 2) => 2 * (2 * X - 1) * Tp (k + 1) - Tp k

noncomputable def Mp : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 2 * X + 1
  | (k + 2) => (4 * X + 2) * Mp (k + 1) + Mp k

lemma Tp_eval (x : ℝ) (k : ℕ) :
    (Tp k).eval (Real.cos x ^ 2) = Real.cos (2 * k * x) ∧
    (Tp (k + 1)).eval (Real.cos x ^ 2) = Real.cos (2 * (k + 1 : ℕ) * x) := by
  induction k with
  | zero =>
    refine ⟨by simp [Tp], ?_⟩
    simp [Tp, Real.cos_two_mul]
  | succ k ih =>
    refine ⟨by rw [ih.2], ?_⟩
    have e : Tp (k + 1 + 1) = 2 * (2 * X - 1) * Tp (k + 1) - Tp k := rfl
    rw [e]
    simp only [eval_sub, eval_mul, eval_ofNat, eval_X, eval_one, ih.1, ih.2]
    have h1 : Real.cos (2 * ((k + 1 : ℕ) : ℝ) * x + 2 * x) + Real.cos (2 * ((k + 1 : ℕ) : ℝ) * x - 2 * x)
        = 2 * Real.cos (2 * ((k + 1 : ℕ) : ℝ) * x) * Real.cos (2 * x) := by
      rw [Real.cos_add, Real.cos_sub]; ring
    have h2 : Real.cos (2 * x) = 2 * Real.cos x ^ 2 - 1 := Real.cos_two_mul x
    have h3 : 2 * ((k + 1 + 1 : ℕ) : ℝ) * x = 2 * ((k + 1 : ℕ) : ℝ) * x + 2 * x := by push_cast; ring
    have h4 : 2 * (k : ℝ) * x = 2 * ((k + 1 : ℕ) : ℝ) * x - 2 * x := by push_cast; ring
    rw [h3, h4]
    rw [h2] at h1
    push_cast at h1 ⊢
    linarith

lemma Mp_eval_one (k : ℕ) : (Mp k).eval 1 ≤ 7 ^ k ∧ (Mp (k + 1)).eval 1 ≤ 7 ^ (k + 1) := by
  induction k with
  | zero => simp [Mp]; norm_num
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    have e : Mp (k + 1 + 1) = (4 * X + 2) * Mp (k + 1) + Mp k := rfl
    rw [e]
    simp only [eval_add, eval_mul, eval_ofNat, eval_X]
    have h7 : (0 : ℝ) < 7 ^ k := by positivity
    have p1 := pow_succ (7:ℝ) k
    have p2 := pow_succ (7:ℝ) (k + 1)
    linarith [ih.1, ih.2, h7]

lemma Mp_natDegree (k : ℕ) : (Mp k).natDegree ≤ k ∧ (Mp (k + 1)).natDegree ≤ k + 1 := by
  induction k with
  | zero =>
    refine ⟨by simp [Mp], ?_⟩
    simp only [Mp]; compute_degree
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    have e : Mp (k + 1 + 1) = (4 * X + 2) * Mp (k + 1) + Mp k := rfl
    rw [e]
    have h1 : ((4 : ℝ[X]) * X + 2).natDegree ≤ 1 := by compute_degree
    refine (natDegree_add_le _ _).trans (max_le ?_ (by omega))
    refine (natDegree_mul_le).trans ?_
    omega

lemma coeff_ofNat_mul' (n : ℕ) [n.AtLeastTwo] (p : ℝ[X]) (j : ℕ) :
    ((OfNat.ofNat n : ℝ[X]) * p).coeff j = (OfNat.ofNat n : ℝ) * p.coeff j := by
  simp

lemma coeff_X_mul' (p : ℝ[X]) (j : ℕ) : (X * p).coeff j = if j = 0 then 0 else p.coeff (j - 1) := by
  rcases j with _ | j
  · simp
  · simp [coeff_X_mul]

lemma Tp_maj (k : ℕ) :
    ((∀ j, |(Tp k).coeff j| ≤ (Mp k).coeff j) ∧ (∀ j, 0 ≤ (Mp k).coeff j)) ∧
    ((∀ j, |(Tp (k + 1)).coeff j| ≤ (Mp (k + 1)).coeff j) ∧ (∀ j, 0 ≤ (Mp (k + 1)).coeff j)) := by
  induction k with
  | zero =>
    refine ⟨⟨fun j => ?_, fun j => ?_⟩, ⟨fun j => ?_, fun j => ?_⟩⟩
    · simp only [Tp, Mp]; by_cases hj : j = 0 <;> simp [coeff_one, hj]
    · simp only [Mp]; by_cases hj : j = 0 <;> simp [coeff_one, hj]
    · simp only [Tp, Mp]
      rcases j with _ | _ | j <;> simp [coeff_one, coeff_X, coeff_sub, coeff_add] <;> norm_num
    · simp only [Mp]
      rcases j with _ | _ | j <;> simp [coeff_one, coeff_X] <;> norm_num
  | succ k ih =>
    obtain ⟨⟨hT0, hM0⟩, ⟨hT1, hM1⟩⟩ := ih
    refine ⟨⟨hT1, hM1⟩, ?_, ?_⟩
    · intro j
      have c4 : (C (4:ℝ)) = (4:ℝ[X]) := map_ofNat C 4
      have c2 : (C (2:ℝ)) = (2:ℝ[X]) := map_ofNat C 2
      have e1 : Tp (k + 1 + 1) = C 4 * (X * Tp (k + 1)) - C 2 * Tp (k + 1) - Tp k := by
        rw [c4, c2]; show 2 * (2 * X - 1) * Tp (k + 1) - Tp k = _; ring
      have e2 : Mp (k + 1 + 1) = C 4 * (X * Mp (k + 1)) + C 2 * Mp (k + 1) + Mp k := by
        rw [c4, c2]; show (4 * X + 2) * Mp (k + 1) + Mp k = _; ring
      rw [e1, e2]
      simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_mul']
      have a1 := hT1 j; have a2 := hT0 j; have a3 := hM1 j
      have b1 : |if j = 0 then (0:ℝ) else (Tp (k + 1)).coeff (j - 1)| ≤ if j = 0 then 0 else (Mp (k + 1)).coeff (j - 1) := by
        split_ifs
        · simp
        · exact hT1 _
      have b2 : 0 ≤ if j = 0 then (0:ℝ) else (Mp (k + 1)).coeff (j - 1) := by
        split_ifs
        · exact le_refl _
        · exact hM1 _
      generalize (if j = 0 then (0:ℝ) else (Tp (k + 1)).coeff (j - 1)) = A at b1 ⊢
      generalize (if j = 0 then (0:ℝ) else (Mp (k + 1)).coeff (j - 1)) = B at b1 b2 ⊢
      rw [abs_le] at a1 a2 b1 ⊢
      have := hM0 j
      constructor <;> nlinarith [a1.1, a1.2, a2.1, a2.2, b1.1, b1.2]
    · intro j
      have c4 : (C (4:ℝ)) = (4:ℝ[X]) := map_ofNat C 4
      have c2 : (C (2:ℝ)) = (2:ℝ[X]) := map_ofNat C 2
      have e2 : Mp (k + 1 + 1) = C 4 * (X * Mp (k + 1)) + C 2 * Mp (k + 1) + Mp k := by
        rw [c4, c2]; show (4 * X + 2) * Mp (k + 1) + Mp k = _; ring
      rw [e2]
      simp only [coeff_add, coeff_C_mul, coeff_X_mul']
      have : 0 ≤ if j = 0 then (0:ℝ) else (Mp (k + 1)).coeff (j - 1) := by
        split_ifs
        · exact le_refl _
        · exact hM1 _
      have := hM1 j; have := hM0 j
      nlinarith

lemma coeff_le_eval_one (p : ℝ[X]) (hp : ∀ j, 0 ≤ p.coeff j) (j : ℕ) : p.coeff j ≤ p.eval 1 := by
  have hn : p.natDegree < max (p.natDegree + 1) (j + 1) := by omega
  rw [eval_eq_sum_range' hn]
  simp only [one_pow, mul_one]
  exact Finset.single_le_sum (f := fun i => p.coeff i) (fun i _ => hp i)
    (Finset.mem_range.mpr (by omega))

lemma Tp_coeff_le (k j : ℕ) : |(Tp k).coeff j| ≤ 7 ^ k := by
  have h1 := ((Tp_maj k).1.1 j).trans (coeff_le_eval_one _ (Tp_maj k).1.2 j)
  exact h1.trans (Mp_eval_one k).1

lemma Tp_natDegree (k : ℕ) : (Tp k).natDegree ≤ k := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro j hj
  have h1 := (Tp_maj k).1.1 j
  have h2 : (Mp k).coeff j = 0 := coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (Mp_natDegree k).1 hj)
  rw [h2] at h1
  exact abs_nonpos_iff.mp h1

noncomputable def Qp (K : ℕ) : ℝ[X] := ∑ k ∈ Finset.range (K + 1), C (bb k) * Tp k

lemma Qp_eval (K : ℕ) (x : ℝ) :
    (Qp K).eval (Real.cos x ^ 2) = ∑ k ∈ Finset.range (K + 1), bb k * Real.cos (2 * k * x) := by
  simp only [Qp, eval_finsetSum, eval_mul, eval_C]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [(Tp_eval x k).1]

lemma Qp_natDegree (K : ℕ) : (Qp K).natDegree ≤ K := by
  refine natDegree_sum_le_of_forall_le _ _ (fun k hk => ?_)
  have := Finset.mem_range.mp hk
  exact (natDegree_C_mul_le _ _).trans ((Tp_natDegree k).trans (by omega))

lemma Qp_coeff (K j : ℕ) : |(Qp K).coeff j| ≤ 4 * 7 ^ K := by
  simp only [Qp, finsetSum_coeff, coeff_C_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k ∈ Finset.range (K + 1), |bb k * (Tp k).coeff j|
      ≤ ∑ k ∈ Finset.range (K + 1), |bb k| * 7 ^ K := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        rw [abs_mul]
        have hk' := Finset.mem_range.mp hk
        have : (7:ℝ) ^ k ≤ 7 ^ K := pow_le_pow_right₀ (by norm_num) (by omega)
        exact mul_le_mul_of_nonneg_left ((Tp_coeff_le k j).trans this) (abs_nonneg _)
    _ = (∑ k ∈ Finset.range (K + 1), |bb k|) * 7 ^ K := by rw [Finset.sum_mul]
    _ ≤ 4 * 7 ^ K := by
        have := bb_sum_le K
        have h7 : (0:ℝ) < 7 ^ K := by positivity
        nlinarith

lemma four_seven_le (K : ℕ) (hK : 12 ≤ K) : (4 : ℝ) * 7 ^ K ≤ 8 ^ K := by
  induction K, hK using Nat.le_induction with
  | base => norm_num
  | succ K hK ih =>
    rw [pow_succ, pow_succ]
    have : (0:ℝ) < 7 ^ K := by positivity
    nlinarith

theorem solution :
    ∃ C_poly : ℝ, ∀ K : ℕ, 1 ≤ K →
      ∃ a : Fin (K + 1) → ℝ, (∀ j, |a j| ≤ (2 : ℝ) ^ (3 * K)) ∧
        ∀ u ∈ Set.Icc (0 : ℝ) 1,
          |∑ j : Fin (K + 1), a j * u ^ (j : ℕ) - Real.sqrt u| ≤ C_poly / K := by
  refine ⟨12, fun K hK => ?_⟩
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  by_cases hK12 : K < 12
  · refine ⟨fun _ => 0, fun j => by rw [abs_zero]; positivity, fun u hu => ?_⟩
    simp only [zero_mul, Finset.sum_const_zero, zero_sub, abs_neg]
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    have h1 : Real.sqrt u ≤ 1 := by
      rw [Real.sqrt_le_one]; exact hu.2
    have h2 : (K : ℝ) ≤ 12 := by exact_mod_cast hK12.le
    rw [le_div_iff₀ hKpos]
    nlinarith
  · rw [not_lt] at hK12
    refine ⟨fun j => (Qp K).coeff j, fun j => ?_, fun u hu => ?_⟩
    · have h1 := Qp_coeff K j
      have h2 := four_seven_le K hK12
      calc |(Qp K).coeff j| ≤ 4 * 7 ^ K := h1
        _ ≤ 8 ^ K := h2
        _ = (2:ℝ) ^ (3 * K) := by rw [pow_mul]; norm_num
    · have hsq : Real.sqrt u ≤ 1 := by rw [Real.sqrt_le_one]; exact hu.2
      set x := Real.arccos (Real.sqrt u) with hx
      have hc : Real.cos x = Real.sqrt u :=
        Real.cos_arccos (by linarith [Real.sqrt_nonneg u]) hsq
      have hcu : Real.cos x ^ 2 = u := by rw [hc, Real.sq_sqrt hu.1]
      have habs : |Real.cos x| = Real.sqrt u := by rw [hc, abs_of_nonneg (Real.sqrt_nonneg _)]
      have hev : ∑ j : Fin (K + 1), (Qp K).coeff j * u ^ (j : ℕ) = (Qp K).eval u := by
        rw [eval_eq_sum_range' (Nat.lt_succ_of_le (Qp_natDegree K))]
        exact Fin.sum_univ_eq_sum_range (fun j => (Qp K).coeff j * u ^ j) (K + 1)
      have hq := Qp_eval K x
      rw [hcu] at hq
      rw [hev, hq, ← habs, ← abs_neg, neg_sub]
      refine (abs_cos_tail x K).trans ?_
      have hp3 : (3 : ℝ) < π := Real.pi_gt_three
      have h8 : 8 / π ≤ 3 := by rw [div_le_iff₀ Real.pi_pos]; linarith
      calc 8 / π / ((K : ℝ) + 1) ≤ 3 / ((K : ℝ) + 1) := by gcongr
        _ ≤ 3 / K := by gcongr; linarith
        _ ≤ 12 / K := by gcongr; norm_num

end PartF
