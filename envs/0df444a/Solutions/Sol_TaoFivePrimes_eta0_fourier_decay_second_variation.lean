-- Prove2me | solution 1 for TaoFivePrimes.eta0_fourier_decay_second_variation
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T23:50:46.582872+00:00
-- url     : https://prove2.me/submissions/fc2c2cb4-332c-4276-ad4b-ac8258d49705

import Mathlib
import Definitions.Def_TaoFivePrimes_SmoothedExpSum
import Theorems.Thm_TaoFivePrimes_eta0_lipschitz_sixteen
import Definitions.Def_TaoFivePrimes_RepresentationCount

open MeasureTheory
open TaoFivePrimes

namespace Eta0FourierSecond

theorem eta0_eq_zero_of_le {t : ℝ} (h : t ≤ 1/4) : eta0 t = 0 := by
  unfold eta0
  by_cases ht : 0 < t
  · rw [if_pos ht, max_eq_left, mul_zero]
    have h2 : Real.log (2*t) ≤ Real.log (1/2) := Real.log_le_log (by linarith) (by linarith)
    have h3 : Real.log (1/2 : ℝ) = -Real.log 2 := by
      rw [show (1/2 : ℝ) = (2:ℝ)⁻¹ by norm_num, Real.log_inv]
    rw [h3] at h2
    linarith [neg_le_abs (Real.log (2*t))]
  · rw [if_neg ht]

theorem eta0_eq_zero_of_ge {t : ℝ} (h : 1 ≤ t) : eta0 t = 0 := by
  unfold eta0
  have ht : 0 < t := by linarith
  rw [if_pos ht, max_eq_left, mul_zero]
  have h2 : Real.log 2 ≤ Real.log (2*t) := Real.log_le_log (by norm_num) (by linarith)
  linarith [le_abs_self (Real.log (2*t))]

theorem eta0_on_left {t : ℝ} (h1 : 1/4 ≤ t) (h2 : t ≤ 1/2) :
    eta0 t = 4 * (2 * Real.log 2 + Real.log t) := by
  have ht : 0 < t := by linarith
  have hlog : Real.log (2*t) = Real.log 2 + Real.log t :=
    Real.log_mul (by norm_num) (ne_of_gt ht)
  have hle : Real.log (2*t) ≤ 0 := by
    rw [show (0:ℝ) = Real.log 1 by simp]
    exact Real.log_le_log (by linarith) (by linarith)
  have hge : (0:ℝ) ≤ 2 * Real.log 2 + Real.log t := by
    have h : Real.log (1/4 : ℝ) ≤ Real.log t := Real.log_le_log (by norm_num) h1
    have h4 : Real.log (1/4 : ℝ) = -(2 * Real.log 2) := by
      rw [show (1/4 : ℝ) = (2:ℝ)⁻¹ ^ 2 by norm_num, Real.log_pow, Real.log_inv]
      push_cast; ring
    linarith [h4 ▸ h]
  unfold eta0
  rw [if_pos ht, abs_of_nonpos hle, hlog, max_eq_right (by linarith)]
  ring

theorem eta0_on_right {t : ℝ} (h1 : 1/2 ≤ t) (h2 : t ≤ 1) :
    eta0 t = -4 * Real.log t := by
  have ht : 0 < t := by linarith
  have hlog : Real.log (2*t) = Real.log 2 + Real.log t :=
    Real.log_mul (by norm_num) (ne_of_gt ht)
  have hge : (0:ℝ) ≤ Real.log (2*t) := by
    rw [show (0:ℝ) = Real.log 1 by simp]
    exact Real.log_le_log (by norm_num) (by linarith)
  have hlt : Real.log t ≤ 0 := by
    rw [show (0:ℝ) = Real.log 1 by simp]
    exact Real.log_le_log ht h2
  unfold eta0
  rw [if_pos ht, abs_of_nonneg hge, hlog, max_eq_right (by linarith)]
  ring

private lemma twice_parts (a b : ℝ) (u u' u'' f f' f'' : ℝ → ℂ)
    (hu : ∀ t ∈ Set.uIcc a b, HasDerivAt u (u' t) t)
    (hu' : ∀ t ∈ Set.uIcc a b, HasDerivAt u' (u'' t) t)
    (hf : ∀ t ∈ Set.uIcc a b, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Set.uIcc a b, HasDerivAt f' (f'' t) t)
    (hiu' : IntervalIntegrable u' volume a b)
    (hiu'' : IntervalIntegrable u'' volume a b)
    (hif' : IntervalIntegrable f' volume a b)
    (hif'' : IntervalIntegrable f'' volume a b) :
    (∫ t in a..b, u t * f'' t) =
      u b * f' b - u a * f' a - u' b * f b + u' a * f a +
        ∫ t in a..b, u'' t * f t := by
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hf' hiu' hif'',
    intervalIntegral.integral_mul_deriv_eq_deriv_mul hu' hf hiu'' hif']
  ring

private lemma branch_parts (a b C D : ℝ) (ha : 0 < a) (hb : 0 < b)
    (f f' f'' : ℝ → ℂ) (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : ∀ t, HasDerivAt f' (f'' t) t) (hc : Continuous f'') :
    (∫ t in a..b, ((C + D * Real.log t : ℝ) : ℂ) * f'' t) =
      ((C + D * Real.log b : ℝ) : ℂ) * f' b -
      ((C + D * Real.log a : ℝ) : ℂ) * f' a -
      ((D / b : ℝ) : ℂ) * f b + ((D / a : ℝ) : ℂ) * f a +
        ∫ t in a..b, ((-D / t ^ 2 : ℝ) : ℂ) * f t := by
  have hn : ∀ t ∈ Set.uIcc a b, t ≠ 0 := by
    intro t ht
    exact ne_of_gt (lt_of_lt_of_le (lt_min ha hb) ht.1)
  apply twice_parts a b (fun t => ((C + D * Real.log t : ℝ) : ℂ))
    (fun t => ((D / t : ℝ) : ℂ)) (fun t => ((-D / t ^ 2 : ℝ) : ℂ)) f f' f''
  · intro t ht
    have hr : HasDerivAt (fun s : ℝ => C + D * Real.log s) (D / t) t := by
      simpa only [div_eq_mul_inv] using
        ((Real.hasDerivAt_log (hn t ht)).const_mul D).const_add C
    exact hr.ofReal_comp
  · intro t ht
    have hr : HasDerivAt (fun s : ℝ => D / s) (-D / t ^ 2) t := by
      simpa only [div_eq_mul_inv, mul_neg, neg_mul] using
        (hasDerivAt_inv (hn t ht)).const_mul D
    exact hr.ofReal_comp
  · intro t ht; exact hf t
  · intro t ht; exact hf' t
  · exact (Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_const.div continuousOn_id hn)).intervalIntegrable
  · exact (Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_const.div (continuousOn_id.pow 2)
        (fun t ht => pow_ne_zero 2 (hn t ht)))).intervalIntegrable
  · exact (continuous_iff_continuousAt.mpr (fun t => (hf' t).continuousAt)).intervalIntegrable a b
  · exact hc.intervalIntegrable a b

private lemma weak_identity (f f' f'' : ℝ → ℂ)
    (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : ∀ t, HasDerivAt f' (f'' t) t) (hc : Continuous f'') :
    (∫ t in (1 / 4 : ℝ)..1, (eta0 t : ℂ) * f'' t) =
      16 * f (1 / 4) - 16 * f (1 / 2) + 4 * f 1 +
        (∫ t in (1 / 2 : ℝ)..1, ((4 / t ^ 2 : ℝ) : ℂ) * f t) -
        (∫ t in (1 / 4 : ℝ)..(1 / 2), ((4 / t ^ 2 : ℝ) : ℂ) * f t) := by
  have hleft := branch_parts (1/4) (1/2) (8 * Real.log 2) 4 (by norm_num)
    (by norm_num) f f' f'' hf hf' hc
  have hright := branch_parts (1/2) 1 0 (-4) (by norm_num)
    (by norm_num) f f' f'' hf hf' hc
  have loghalf : Real.log (1/2 : ℝ) = -Real.log 2 := by
    rw [show (1/2 : ℝ) = (2:ℝ)⁻¹ by norm_num, Real.log_inv]
  have logquarter : Real.log (1/4 : ℝ) = -(2 * Real.log 2) := by
    rw [show (1/4 : ℝ) = ((2:ℝ)⁻¹)^2 by norm_num, Real.log_pow, Real.log_inv]
    ring
  have hi : Continuous (fun t => (eta0 t : ℂ) * f'' t) :=
    (Complex.continuous_ofReal.comp eta0_lipschitz_sixteen.continuous).mul hc
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hi.intervalIntegrable (1/4) (1/2)) (hi.intervalIntegrable (1/2) 1)]
  have heqleft : (∫ t in (1/4 : ℝ)..(1/2), (eta0 t : ℂ) * f'' t) =
      ∫ t in (1/4 : ℝ)..(1/2), ((8 * Real.log 2 + 4 * Real.log t : ℝ) : ℂ) * f'' t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (1/4:ℝ) ≤ 1/2)] at ht
    change (eta0 t : ℂ) * f'' t = _
    rw [eta0_on_left ht.1 ht.2]
    push_cast
    ring
  have heqright : (∫ t in (1/2 : ℝ)..1, (eta0 t : ℂ) * f'' t) =
      ∫ t in (1/2 : ℝ)..1, ((0 + -4 * Real.log t : ℝ) : ℂ) * f'' t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 1)] at ht
    change (eta0 t : ℂ) * f'' t = _
    rw [eta0_on_right ht.1 ht.2]
    ring
  rw [heqleft, heqright, hleft, hright, loghalf, logquarter]
  simp only [Real.log_one, mul_zero, add_zero]
  have hneg : (∫ t in (1/4 : ℝ)..(1/2), ((-4 / t ^ 2 : ℝ) : ℂ) * f t) =
      -(∫ t in (1/4 : ℝ)..(1/2), ((4 / t ^ 2 : ℝ) : ℂ) * f t) := by
    simp only [neg_div, Complex.ofReal_neg, neg_mul, intervalIntegral.integral_neg]
  rw [hneg]
  norm_num
  push_cast
  ring

private lemma weighted_integral_bound (a b M : ℝ) (f : ℝ → ℂ)
    (ha : 0 < a) (hab : a ≤ b)
    (hM : ∀ t ∈ Set.Ioc a b, ‖f t‖ ≤ M) :
    ‖∫ t in a..b, ((4 / t ^ 2 : ℝ) : ℂ) * f t‖ ≤ 4 * (a⁻¹ - b⁻¹) * M := by
  have hn : ∀ t ∈ Set.uIcc a b, t ≠ 0 := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact ne_of_gt (lt_of_lt_of_le ha ht.1)
  have hi : IntervalIntegrable (fun t : ℝ => (4 / t ^ 2) * M) volume a b :=
    ((continuousOn_const.div (continuousOn_id.pow 2)
      (fun t ht => pow_ne_zero 2 (hn t ht))).mul continuousOn_const).intervalIntegrable
  have h := intervalIntegral.norm_integral_le_of_norm_le hab
    (g := fun t : ℝ => (4 / t ^ 2) * M)
    (f := fun t : ℝ => ((4 / t ^ 2 : ℝ) : ℂ) * f t)
    (Filter.Eventually.of_forall (fun t ht => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (by norm_num) (sq_nonneg t))]
      exact mul_le_mul_of_nonneg_left (hM t ht)
        (div_nonneg (by norm_num) (sq_nonneg t)))) hi
  rw [intervalIntegral.integral_mul_const] at h
  have hpow : ∀ t : ℝ, (4 : ℝ) / t ^ 2 = 4 * t ^ (-2 : ℤ) := by
    intro t
    simp [zpow_neg, div_eq_mul_inv]
  simp only [hpow] at h
  rw [intervalIntegral.integral_const_mul, integral_zpow (n := (-2 : ℤ)) (Or.inr ⟨by norm_num, by
    intro ht
    exact hn 0 ht rfl⟩)] at h
  simp only [hpow]
  convert h using 1 <;> norm_num <;> ring <;> simp

private lemma weak_bound (f f' f'' : ℝ → ℂ)
    (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : ∀ t, HasDerivAt f' (f'' t) t) (hc : Continuous f'')
    (M : ℝ) (hM : ∀ t ∈ Set.Icc (1 / 4 : ℝ) 1, ‖f t‖ ≤ M) :
    ‖∫ t in (1 / 4 : ℝ)..1, (eta0 t : ℂ) * f'' t‖ ≤ 48 * M := by
  rw [weak_identity f f' f'' hf hf' hc]
  have hleft := weighted_integral_bound (1/4) (1/2) M f (by norm_num) (by norm_num)
    (fun t ht => hM t ⟨le_of_lt ht.1, le_trans ht.2 (by norm_num)⟩)
  have hright := weighted_integral_bound (1/2) 1 M f (by norm_num) (by norm_num)
    (fun t ht => hM t ⟨by linarith [ht.1], ht.2⟩)
  norm_num at hleft hright
  have ha := hM (1/4) (by norm_num)
  have hb := hM (1/2) (by norm_num)
  have hc1 := hM 1 (by norm_num)
  have h1 := norm_sub_le (16 * f (1/4)) (16 * f (1/2))
  have h2 := norm_add_le (16 * f (1/4) - 16 * f (1/2)) (4 * f 1)
  have h3 := norm_add_le (16 * f (1/4) - 16 * f (1/2) + 4 * f 1)
    (∫ t in (1/2 : ℝ)..1, ((4 / t ^ 2 : ℝ) : ℂ) * f t)
  have h4 := norm_sub_le (16 * f (1/4) - 16 * f (1/2) + 4 * f 1 +
    (∫ t in (1/2 : ℝ)..1, ((4 / t ^ 2 : ℝ) : ℂ) * f t))
    (∫ t in (1/4 : ℝ)..(1/2), ((4 / t ^ 2 : ℝ) : ℂ) * f t)
  norm_num [norm_mul] at h1 h2
  push_cast at h3 h4 ⊢
  linarith

end Eta0FourierSecond

open Eta0FourierSecond

theorem solution (beta : ℝ) (hbeta : beta ≠ 0) :
    ‖∫ t : ℝ, (eta0 t : ℂ) * expCircle (beta * t)‖ ≤
      48 / (2 * Real.pi * beta) ^ 2 := by
  let K : ℂ := 2 * Real.pi * Complex.I * beta
  let f : ℝ → ℂ := fun t => Complex.exp (K * t)
  have hf : ∀ t, HasDerivAt f (K * f t) t := by
    intro t
    have h := (((hasDerivAt_id t).ofReal_comp).const_mul K).cexp
    simpa only [f, id_eq, Complex.ofReal_one, mul_one, one_mul, mul_comm] using h
  have hf' : ∀ t, HasDerivAt (fun s => K * f s) (K ^ 2 * f t) t := by
    intro t
    simpa only [pow_two, mul_assoc] using (hf t).const_mul K
  have hfc : Continuous f := by unfold f; fun_prop
  have hf1 : ∀ t, ‖f t‖ = 1 := by
    intro t
    simp [f, K, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  have h := weak_bound f (fun t => K * f t) (fun t => K ^ 2 * f t)
    hf hf' (continuous_const.mul hfc) 1 (fun t ht => (hf1 t).le)
  have hfactor : (∫ t in (1/4 : ℝ)..1, (eta0 t : ℂ) * (K ^ 2 * f t)) =
      K ^ 2 * ∫ t in (1/4 : ℝ)..1, (eta0 t : ℂ) * f t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp
    ring
  rw [hfactor, norm_mul, norm_pow] at h
  have hKn : ‖K‖ ^ 2 = (2 * Real.pi * beta) ^ 2 := by
    simp [K, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs] <;> ring
  rw [hKn] at h
  have hcompl : ∀ t ∈ (Set.Icc (1/4 : ℝ) 1)ᶜ, (eta0 t : ℂ) * expCircle (beta * t) = 0 := by
    intro t ht
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at ht
    rcases ht with ht | ht
    · rw [eta0_eq_zero_of_le (le_of_lt ht)]; simp
    · rw [eta0_eq_zero_of_ge (le_of_lt ht)]; simp
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hcompl,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (1/4 : ℝ) ≤ 1)]
  have he : ∀ t, expCircle (beta * t) = f t := by
    intro t
    unfold expCircle f K
    congr 1
    push_cast
    ring
  simp only [he]
  apply (le_div_iff₀ (sq_pos_of_ne_zero (mul_ne_zero
    (mul_ne_zero (by norm_num) Real.pi_ne_zero) hbeta))).2
  simpa only [mul_one, one_mul, mul_comm] using h
