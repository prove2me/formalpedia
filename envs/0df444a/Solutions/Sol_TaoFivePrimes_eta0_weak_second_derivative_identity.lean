-- Prove2me | solution 1 for TaoFivePrimes.eta0_weak_second_derivative_identity
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T23:07:15.607882+00:00
-- url     : https://prove2.me/submissions/448f7876-d08d-44dd-ba15-536694492f5f

import Mathlib
import Theorems.Thm_TaoFivePrimes_eta0_lipschitz_sixteen
import Definitions.Def_TaoFivePrimes_RepresentationCount

open MeasureTheory
open TaoFivePrimes

namespace Eta0WeakSecond

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

private lemma twice_parts (a b : ℝ) (u u' u'' f f' f'' : ℝ → ℝ)
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
    (f f' f'' : ℝ → ℝ) (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : ∀ t, HasDerivAt f' (f'' t) t) (hc : Continuous f'') :
    (∫ t in a..b, (C + D * Real.log t) * f'' t) =
      (C + D * Real.log b) * f' b - (C + D * Real.log a) * f' a -
      D / b * f b + D / a * f a +
        ∫ t in a..b, (-D / t ^ 2) * f t := by
  have hn : ∀ t ∈ Set.uIcc a b, t ≠ 0 := by
    intro t ht
    have hp : 0 < min a b := lt_min ha hb
    exact ne_of_gt (lt_of_lt_of_le hp ht.1)
  apply twice_parts a b (fun t => C + D * Real.log t)
    (fun t => D / t) (fun t => -D / t ^ 2) f f' f''
  · intro t ht
    simpa only [div_eq_mul_inv] using
      ((Real.hasDerivAt_log (hn t ht)).const_mul D).const_add C
  · intro t ht
    simpa only [div_eq_mul_inv, mul_neg, neg_mul] using
      (hasDerivAt_inv (hn t ht)).const_mul D
  · intro t ht; exact hf t
  · intro t ht; exact hf' t
  · exact (continuousOn_const.div continuousOn_id hn).intervalIntegrable
  · exact (continuousOn_const.div (continuousOn_id.pow 2)
      (fun t ht => pow_ne_zero 2 (hn t ht))).intervalIntegrable
  · exact (continuous_iff_continuousAt.mpr (fun t => (hf' t).continuousAt)).intervalIntegrable a b
  · exact hc.intervalIntegrable a b

end Eta0WeakSecond

open Eta0WeakSecond

theorem solution (f f' f'' : ℝ → ℝ)
    (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : ∀ t, HasDerivAt f' (f'' t) t) (hc : Continuous f'') :
    (∫ t in (1 / 4 : ℝ)..1, TaoFivePrimes.eta0 t * f'' t) =
      16 * f (1 / 4) - 16 * f (1 / 2) + 4 * f 1 +
        (∫ t in (1 / 2 : ℝ)..1, (4 / t ^ 2) * f t) -
        (∫ t in (1 / 4 : ℝ)..(1 / 2), (4 / t ^ 2) * f t) := by
  have hleft := branch_parts (1/4) (1/2) (8 * Real.log 2) 4 (by norm_num)
    (by norm_num) f f' f'' hf hf' hc
  have hright := branch_parts (1/2) 1 0 (-4) (by norm_num)
    (by norm_num) f f' f'' hf hf' hc
  have loghalf : Real.log (1/2 : ℝ) = -Real.log 2 := by
    rw [show (1/2 : ℝ) = (2:ℝ)⁻¹ by norm_num, Real.log_inv]
  have logquarter : Real.log (1/4 : ℝ) = -(2 * Real.log 2) := by
    rw [show (1/4 : ℝ) = ((2:ℝ)⁻¹)^2 by norm_num, Real.log_pow, Real.log_inv]
    ring
  have hi : Continuous (fun t => eta0 t * f'' t) := eta0_lipschitz_sixteen.continuous.mul hc
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hi.intervalIntegrable (1/4) (1/2)) (hi.intervalIntegrable (1/2) 1)]
  have heqleft : (∫ t in (1/4 : ℝ)..(1/2), eta0 t * f'' t) =
      ∫ t in (1/4 : ℝ)..(1/2), (8 * Real.log 2 + 4 * Real.log t) * f'' t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (1/4:ℝ) ≤ 1/2)] at ht
    change eta0 t * f'' t = _
    rw [eta0_on_left ht.1 ht.2]
    ring
  have heqright : (∫ t in (1/2 : ℝ)..1, eta0 t * f'' t) =
      ∫ t in (1/2 : ℝ)..1, (0 + -4 * Real.log t) * f'' t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 1)] at ht
    change eta0 t * f'' t = _
    rw [eta0_on_right ht.1 ht.2]
    ring
  rw [heqleft, heqright, hleft, hright, loghalf, logquarter]
  simp only [Real.log_one, mul_zero, add_zero]
  have hneg : (∫ t in (1/4 : ℝ)..(1/2), (-4 / t ^ 2) * f t) =
      -(∫ t in (1/4 : ℝ)..(1/2), (4 / t ^ 2) * f t) := by
    simp only [neg_div, neg_mul, intervalIntegral.integral_neg]
  rw [hneg]
  norm_num <;> ring
