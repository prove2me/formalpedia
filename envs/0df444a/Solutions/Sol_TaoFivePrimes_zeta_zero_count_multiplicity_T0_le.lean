-- Prove2me | solution 1 for TaoFivePrimes.zeta_zero_count_multiplicity_T0_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-03T02:26:45.801024+00:00
-- url     : https://prove2.me/submissions/b21dca05-292c-49eb-a60d-6441170cf7d0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_zeta_ne_zero_of_mem_strip_of_abs_im_le_two
import Theorems.Thm_TaoFivePrimes_trudgian_zero_count_upper

private lemma zeta_ne_zero_re_zero (s : ℂ) (hre : s.re = 0) : riemannZeta s ≠ 0 := by
  by_cases hs : s = 0
  · subst s
    norm_num [riemannZeta_zero]
  have hsn : ∀ n : ℕ, s ≠ -(n : ℂ) := by
    intro n heq
    have hn : (n : ℝ) = 0 := by
      have := congrArg Complex.re heq
      simp only [Complex.neg_re, Complex.natCast_re] at this
      linarith
    have hn0 : n = 0 := by exact_mod_cast hn
    subst n
    exact hs (by simpa using heq)
  have hs1 : s ≠ 1 := by
    intro heq
    have := congrArg Complex.re heq
    simp_all
  intro hz
  have hfe := riemannZeta_one_sub hsn hs1
  rw [hz, mul_zero] at hfe
  exact riemannZeta_ne_zero_of_one_le_re (by simp [hre]) hfe

private lemma zero_regions_eq (T : ℝ) :
    {s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 ≤ s.im ∧ s.im ≤ T ∧ riemannZeta s = 0} =
    {s : ℂ | 0 < s.re ∧ s.re < 1 ∧ 0 < s.im ∧ s.im ≤ T ∧ riemannZeta s = 0} := by
  ext s
  constructor
  · rintro ⟨hr0, hr1, hi0, hiT, hz⟩
    have hr0' : 0 < s.re := lt_of_le_of_ne hr0 (by
      intro heq
      exact zeta_ne_zero_re_zero s heq.symm hz)
    have hr1' : s.re < 1 := lt_of_le_of_ne hr1 (by
      intro heq
      exact riemannZeta_ne_zero_of_one_le_re (le_of_eq heq.symm) hz)
    have hi0' : 0 < s.im := lt_of_le_of_ne hi0 (by
      intro heq
      exact zeta_ne_zero_of_mem_strip_of_abs_im_le_two s hr0' hr1'
        (by simp [← heq]) hz)
    exact ⟨hr0', hr1', hi0', hiT, hz⟩
  · rintro ⟨hr0, hr1, hi0, hiT, hz⟩
    exact ⟨hr0.le, hr1.le, hi0.le, hiT, hz⟩

set_option autoImplicit false

private lemma exp_twenty_lower : (484000000 : ℝ) ≤ Real.exp 20 := by
  have he : (2.718281 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.718281) he 20
  have hh : Real.exp (20:ℝ) = Real.exp 1 ^ 20 := by
    simpa using Real.exp_nat_mul (1:ℝ) 20
  rw [hh]
  norm_num at hp ⊢
  linarith

private lemma exp_twenty_precise : (485160000 : ℝ) ≤ Real.exp 20 := by
  have he : (2.718281 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.718281) he 20
  have hh : Real.exp (20:ℝ) = Real.exp 1 ^ 20 := by
    simpa using Real.exp_nat_mul (1:ℝ) 20
  rw [hh]
  norm_num at hp ⊢
  linarith

private lemma log_ratio_upper :
    Real.log ((3290000000:ℝ)/(2*Real.pi*Real.exp 1)) ≤ 19.08 := by
  apply (Real.log_le_iff_le_exp (by positivity)).2
  apply (div_le_iff₀ (by positivity : 0 < 2*Real.pi*Real.exp 1)).2
  have hex : Real.exp (20.08:ℝ) ≥ (485160000:ℝ)*1.08 := by
    rw [show (20.08:ℝ)=20+0.08 by norm_num, Real.exp_add]
    exact mul_le_mul exp_twenty_precise (by linarith [Real.add_one_le_exp (0.08:ℝ)]) (by norm_num) (Real.exp_pos _).le
  have hpi := Real.pi_gt_d2.le
  have hh := mul_le_mul hpi hex (by norm_num : (0:ℝ) ≤ 485160000*1.08) Real.pi_pos.le
  have hid : Real.exp (19.08:ℝ)*(2*Real.pi*Real.exp 1) = 2*Real.pi*Real.exp 20.08 := by
    rw [show (20.08:ℝ)=19.08+1 by norm_num, Real.exp_add]
    ring
  rw [hid]
  nlinarith

private lemma log_height_upper : Real.log (3290000000:ℝ) ≤ 22 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  have h2 : (7:ℝ) ≤ Real.exp 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7)
      (show (2.7:ℝ) ≤ Real.exp 1 by linarith [Real.exp_one_gt_d9]) 2
    have hh : Real.exp (2:ℝ) = Real.exp 1 ^ 2 := by
      simpa using Real.exp_nat_mul (1:ℝ) 2
    rw [hh]
    nlinarith
  have hh := mul_le_mul exp_twenty_lower h2 (by norm_num : (0:ℝ) ≤ 7) (Real.exp_pos _).le
  rw [← Real.exp_add] at hh
  norm_num at hh
  linarith

private theorem trudgian_numeric :
      (3290000000:ℝ) / (2 * Real.pi) * Real.log (3290000000 / (2 * Real.pi * Real.exp 1)) + 7 / 8
        + 0.112 * Real.log 3290000000 + 0.278 * Real.log (Real.log 3290000000) + 2.51 + 0.2 / 3290000000 ≤ 10000000000 := by
  have hlog := log_height_upper
  have hlogpos : 0 < Real.log (3290000000:ℝ) := Real.log_pos (by norm_num)
  have hloglog : Real.log (Real.log (3290000000:ℝ)) ≤ 22 := by
    have hh := Real.log_le_sub_one_of_pos hlogpos
    linarith
  have hdiv : (3290000000:ℝ)/(2*Real.pi) ≤ 3290000000 / 6.28 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    linarith [Real.pi_gt_d2]
  have hm1 := mul_le_mul_of_nonneg_left log_ratio_upper
    (by positivity : (0:ℝ) ≤ 3290000000/(2*Real.pi))
  have hm2 := mul_le_mul_of_nonneg_right hdiv (by norm_num : (0:ℝ) ≤ 19.08)
  have hm := hm1.trans hm2
  norm_num at hm
  linarith


theorem solution :
    (∑ᶠ s ∈ {s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 ≤ s.im ∧ s.im ≤ 3.29 * 10 ^ 9 ∧
        riemannZeta s = 0}, (analyticOrderNatAt riemannZeta s : ℝ)) ≤ (10 : ℝ) ^ 10 := by
  rw [zero_regions_eq]
  have he : Real.exp 1 ≤ (3.29 : ℝ) * 10 ^ 9 := by
    linarith [Real.exp_one_lt_d9]
  have ht := TaoFivePrimes.trudgian_zero_count_upper ((3.29 : ℝ) * 10 ^ 9) he
  have hn := trudgian_numeric
  norm_num at ht hn ⊢
  exact ht.trans hn
