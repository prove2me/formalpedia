-- Prove2me | solution 1 for SecretaryPred.LearnedDynkin.numerical_bounds
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-26T07:02:51.791795+00:00
-- url     : https://prove2.me/submissions/32f19148-b7f2-48ac-878e-2eaff975f1da

import Definitions.Def_SecretaryPred_LearnedDynkin_Setting
import Init
import Mathlib


section
set_option autoImplicit false
namespace Queelius.SecretaryPred.Numerics
open MeasureTheory
open scoped BigOperators

noncomputable def altSum (m : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 m, (m.choose k:ℝ)*(-1:ℝ)^(k-1)*(1-t^k)/(k:ℝ)

noncomputable def positiveSum (m : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range m, (1-t)^(j+1)/(j+1:ℕ)

theorem sum_Icc_shift (m : ℕ) (f : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 m, f k = ∑ j ∈ Finset.range m, f (j+1) := by
  rw [← Finset.Ico_succ_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp [Nat.add_comm]

theorem binomial_integrand (m : ℕ) (x : ℝ) (hx : x ≠ 0) :
    ∑ j ∈ Finset.range m, (m.choose (j+1):ℝ)*(-x)^j =
      ∑ j ∈ Finset.range m, (1-x)^j := by
  have hb := add_pow (-x) (1:ℝ) m
  rw [Finset.sum_range_succ'] at hb
  simp only [one_pow,mul_one,pow_zero,Nat.choose_zero_right,Nat.cast_one,one_mul] at hb
  have hs : (∑ j ∈ Finset.range m, (m.choose (j+1):ℝ)*(-x)^j)*(-x) =
      ∑ j ∈ Finset.range m, (-x)^(j+1)*(m.choose (j+1):ℝ) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [pow_succ]
    ring
  have hg := geom_sum_mul_neg (1-x) m
  have hm : (∑ j ∈ Finset.range m, (m.choose (j+1):ℝ)*(-x)^j)*x =
      (∑ j ∈ Finset.range m, (1-x)^j)*x := by
    have hp : (-x+1)^m=(1-x)^m := by congr 1; ring
    rw [hp] at hb
    nlinarith
  exact mul_right_cancel₀ hx hm

theorem altSum_eq_positiveSum (m : ℕ) (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    altSum m t = positiveSum m t := by
  have hleft : (∫ x in t..1, ∑ j ∈ Finset.range m, (m.choose (j+1):ℝ)*(-x)^j) = altSum m t := by
    rw [intervalIntegral.integral_finsetSum (f := fun j (x : ℝ) => (m.choose (j+1):ℝ)*(-x)^j) (fun j _ =>
      (by fun_prop : Continuous (fun x : ℝ => (m.choose (j+1):ℝ)*(-x)^j)).intervalIntegrable _ _)]
    rw [altSum, sum_Icc_shift]
    apply Finset.sum_congr rfl
    intro j hj
    rw [show (fun x : ℝ => (m.choose (j+1):ℝ)*(-x)^j) =
        (fun x => ((m.choose (j+1):ℝ)*(-1:ℝ)^j)*x^j) by funext x; rw [neg_pow]; ring]
    rw [intervalIntegral.integral_const_mul,integral_pow]
    simp only [one_pow,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one]
    ring
  have hright : (∫ x in t..1, ∑ j ∈ Finset.range m, (1-x)^j) = positiveSum m t := by
    rw [intervalIntegral.integral_finsetSum (f := fun j (x : ℝ) => (1-x)^j) (fun j _ =>
      (by fun_prop : Continuous (fun x : ℝ => (1-x)^j)).intervalIntegrable _ _)]
    unfold positiveSum
    apply Finset.sum_congr rfl
    intro j hj
    rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x^j) 1,integral_pow]
    simp
  rw [← hleft,← hright]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [Set.uIcc_of_le ht1] at hx
  exact binomial_integrand m x (ne_of_gt (ht0.trans_le hx.1))

theorem positiveSum_nonneg (m : ℕ) (t : ℝ) (ht : t ≤ 1) : 0 ≤ positiveSum m t := by
  apply Finset.sum_nonneg
  intro j hj
  positivity

theorem positiveSum_mono (t : ℝ) (ht : t ≤ 1) : Monotone (fun m => positiveSum m t) := by
  intro m n hmn
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn)
    (fun j _ _ => by positivity)

theorem altSum_nonneg (m : ℕ) (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    0 ≤ altSum m t := by rw [altSum_eq_positiveSum m t ht0 ht1]; exact positiveSum_nonneg m t ht1

theorem altSum_mono (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) : Monotone (fun m => altSum m t) := by
  simpa only [altSum_eq_positiveSum _ t ht0 ht1] using positiveSum_mono t ht1

end Queelius.SecretaryPred.Numerics

end

section
set_option autoImplicit false
namespace Queelius.SecretaryPred.Numerics
open scoped BigOperators

theorem negative_sum (m : ℕ) (t : ℝ) :
    (∑ k ∈ Finset.Icc 1 m, (m.choose k:ℝ)*(-1:ℝ)^k*(1-t^k)/(k:ℝ)) = -altSum m t := by
  rw [altSum,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have h1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hp : (-1:ℝ)^k = -(-1:ℝ)^(k-1) := by
    conv_lhs => rw [← Nat.sub_add_cancel h1]
    rw [pow_succ]
    ring
  rw [hp]
  ring

theorem log_bound : (0.363:ℝ) ≤ 0.313*Real.log (1/0.313) := by
  have h := Real.sum_range_le_log_div (x := (687/1313:ℝ)) (by norm_num) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

theorem basic_case_bound (m : ℕ) (hm : 1 ≤ m) :
    (0.215:ℝ) ≤ 0.313*altSum m 0.313 := by
  rw [altSum_eq_positiveSum _ _ (by norm_num) (by norm_num)]
  have h := positiveSum_mono (0.313:ℝ) (by norm_num) hm
  norm_num [positiveSum,Finset.sum_range_succ] at h ⊢
  linarith

theorem large_m_bound (m : ℕ) (hm : 6 ≤ m) :
    (0.24:ℝ) ≤ 0.313*positiveSum m 0.313 - 0.687/(m:ℝ) := by
  have hs := positiveSum_mono (0.313:ℝ) (by norm_num) hm
  norm_num [positiveSum,Finset.sum_range_succ] at hs ⊢
  have hd : (0.687:ℝ)/(m:ℝ) ≤ 0.687/6 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    exact_mod_cast hm
  linarith

theorem case_v_numeric (m : ℕ) (hm : 1 ≤ m) :
    (0.215:ℝ) ≤ (1-0.313)^(m+1)/((m:ℝ)+1) + 0.313*altSum m 0.313
      - (1-0.313)/(m:ℝ)*(1-(1-0.313)^m) := by
  rw [altSum_eq_positiveSum _ _ (by norm_num) (by norm_num)]
  by_cases h6 : 6 ≤ m
  · have hlarge := large_m_bound m h6
    norm_num at hlarge ⊢
    have hb : 0 ≤ (687/1000/(m:ℝ))*(687/1000:ℝ)^m := by positivity
    have hp : 0 ≤ (687/1000:ℝ)^(m+1)/((m:ℝ)+1) := by positivity
    nlinarith
  · have h5 : m ≤ 5 := by omega
    interval_cases m <;> norm_num [positiveSum,Finset.sum_range_succ]

theorem case_vi_numeric (m : ℕ) (hm : 1 ≤ m) :
    (0.215:ℝ) ≤ 1/((m:ℝ)+1)*((1-0.646)/(1+0.646)) + 0.313*altSum (m+1) 0.313
      - (1-0.313)/((m:ℝ)+1)*(1-(1-0.313)^(m+1)) := by
  rw [altSum_eq_positiveSum _ _ (by norm_num) (by norm_num)]
  by_cases h5 : 5 ≤ m
  · have hlarge := large_m_bound (m+1) (by omega)
    norm_num at hlarge ⊢
    have hb : 0 ≤ (687/1000/((m:ℝ)+1))*(687/1000:ℝ)^(m+1) := by positivity
    have hp : 0 ≤ ((m:ℝ)+1)⁻¹*(177/823:ℝ) := by positivity
    nlinarith
  · have h4 : m ≤ 4 := by omega
    interval_cases m <;> norm_num [positiveSum,Finset.sum_range_succ]

end Queelius.SecretaryPred.Numerics

end

section
open scoped BigOperators
open Queelius.SecretaryPred.Numerics

theorem solution :
    (0.215 : ℝ) ≤ (1 - 0.646) / (1 + 0.646) ∧
      (0.363 : ℝ) ≤ 0.313 * Real.log (1 / 0.313) ∧
      (∀ m : ℕ, 1 ≤ m →
        (0.215 : ℝ) ≤ 1 / ((m : ℝ) + 1) + 0.313 * ∑ k ∈ Finset.Icc 1 m,
          (m.choose k : ℝ) * (-1 : ℝ) ^ (k - 1) * (1 - 0.313 ^ k) / (k : ℝ)) ∧
      (∀ m : ℕ, 1 ≤ m →
        (0.215 : ℝ) ≤ 0.313 * ∑ k ∈ Finset.Icc 1 m,
          (m.choose k : ℝ) * (-1 : ℝ) ^ (k - 1) * (1 - 0.313 ^ k) / (k : ℝ)) ∧
      (∀ m : ℕ, 1 ≤ m →
        (0.215 : ℝ) ≤ (1 - 0.313) ^ (m + 1) / ((m : ℝ) + 1)
          - 0.313 * ∑ k ∈ Finset.Icc 1 m,
              (m.choose k : ℝ) * (-1 : ℝ) ^ k * (1 - 0.313 ^ k) / (k : ℝ)
          - (1 - 0.313) / (m : ℝ) * (1 - (1 - 0.313) ^ m)) ∧
      (∀ m : ℕ, 1 ≤ m →
        (0.215 : ℝ) ≤ 1 / ((m : ℝ) + 1) * ((1 - 0.646) / (1 + 0.646))
          - 0.313 * ∑ k ∈ Finset.Icc 1 (m + 1),
              ((m + 1).choose k : ℝ) * (-1 : ℝ) ^ k * (1 - 0.313 ^ k) / (k : ℝ)
          - (1 - 0.313) / ((m : ℝ) + 1) * (1 - (1 - 0.313) ^ (m + 1))) := by
  refine ⟨by norm_num, log_bound, ?_, ?_, ?_, ?_⟩
  · intro m hm
    change (0.215:ℝ) ≤ 1/((m:ℝ)+1)+0.313*altSum m 0.313
    have h := basic_case_bound m hm
    have hp : (0:ℝ) ≤ 1/((m:ℝ)+1) := by positivity
    linarith
  · intro m hm
    exact basic_case_bound m hm
  · intro m hm
    rw [negative_sum]
    have h := case_v_numeric m hm
    linarith
  · intro m hm
    rw [negative_sum]
    have h := case_vi_numeric m hm
    linarith

end

section
namespace Queelius.SecretaryPred.Numerics
 theorem empty_sum (t : ℝ) : altSum 0 t=0 := by simp [altSum]
 theorem one_term (t : ℝ) : altSum 1 t=1-t := by simp [altSum]
 theorem endpoint_one (m : ℕ) : altSum m 1=0 := by simp [altSum]
 theorem zero_count_fails : ¬ (0.215:ℝ) ≤ 0.313*altSum 0 0.313 := by norm_num [empty_sum]
 theorem cutoff_one_fails (m : ℕ) : ¬ (0.215:ℝ) ≤ altSum m 1 := by norm_num [endpoint_one]
end Queelius.SecretaryPred.Numerics

end
