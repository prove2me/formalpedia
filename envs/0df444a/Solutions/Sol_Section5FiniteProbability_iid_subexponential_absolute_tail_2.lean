-- Prove2me | solution 2 for Section5FiniteProbability.iid_subexponential_absolute_tail
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:19:39.961411+00:00
-- url     : https://prove2.me/submissions/91ae8fde-01fe-4f66-8f46-f03bbed6ca79

import Mathlib
section
set_option autoImplicit false

namespace Section5FiniteProbability

variable {Ω J : Type*} [Fintype Ω] [Fintype J] [DecidableEq J]

theorem weighted_exponential_markov (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (Y : Ω → ℝ) (r l : ℝ) (hl : 0 ≤ l) :
    (∑ x, if r ≤ Y x then p x else 0) ≤
      Real.exp (-l*r)*(∑ x, p x*Real.exp (l*Y x)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  have he : Real.exp (-l*r)*(p x*Real.exp (l*Y x))=
      p x*Real.exp (l*(Y x-r)) := by
    rw [mul_left_comm,← Real.exp_add]
    congr 2
    ring
  rw [he]
  by_cases h : r ≤ Y x
  · rw [if_pos h]
    exact le_mul_of_one_le_right (hp x) (Real.one_le_exp (mul_nonneg hl (sub_nonneg.mpr h)))
  · rw [if_neg h]
    exact mul_nonneg (hp x) (Real.exp_pos _).le

theorem independent_batch_mgf (p : Ω → ℝ) (Y : Ω → ℝ) (l : ℝ) :
    (∑ x : J → Ω, (∏ r, p (x r))*Real.exp (l*(∑ r, Y (x r))))=
      (∑ x, p x*Real.exp (l*Y x))^Fintype.card J := by
  simp only [Finset.mul_sum,Real.exp_sum,← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun _ : J => fun x : Ω => p x*Real.exp (l*Y x))]
  exact Finset.prod_const _

theorem independent_batch_mgf_le (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (Y : Ω → ℝ)
    (l B : ℝ) (h : (∑ x, p x*Real.exp (l*Y x)) ≤ Real.exp B) :
    (∑ x : J → Ω, (∏ r, p (x r))*Real.exp (l*(∑ r, Y (x r)))) ≤
      Real.exp ((Fintype.card J : ℝ)*B) := by
  rw [independent_batch_mgf]
  calc
    _ ≤ (Real.exp B)^Fintype.card J := pow_le_pow_left₀
      (Finset.sum_nonneg (fun x _ => mul_nonneg (hp x) (Real.exp_pos _).le)) h _
    _ = _ := (Real.exp_nat_mul _ _).symm

theorem iid_subexponential_upper_tail (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (Y : Ω → ℝ)
    (hmgf : ∀ l : ℝ, |l| *512 ≤ 1/2 →
      (∑ x, p x*Real.exp (l*Y x)) ≤ Real.exp (8388608*l^2))
    (t : ℝ) (ht : 0 ≤ t) :
    (∑ x : J → Ω, if (Fintype.card J : ℝ)*t ≤ ∑ r, Y (x r) then ∏ r, p (x r) else 0) ≤
      Real.exp (-(Fintype.card J : ℝ)*min (t^2) t/33554432) := by
  let l : ℝ := min t 1/16777216
  have hl0 : 0 ≤ l := div_nonneg (le_min ht (by norm_num)) (by norm_num)
  have hl1 : |l| *512 ≤ 1/2 := by
    rw [abs_of_nonneg hl0]
    have he : min t 1 ≤ 1 := min_le_right _ _
    dsimp [l]
    linarith
  have hbatch := independent_batch_mgf_le (J := J) p hp Y l (8388608*l^2) (hmgf l hl1)
  have hmarkov := weighted_exponential_markov (fun x : J → Ω => ∏ r, p (x r))
    (fun x => Finset.prod_nonneg (fun r _ => hp (x r))) (fun x => ∑ r, Y (x r))
    ((Fintype.card J : ℝ)*t) l hl0
  have hM : 0 ≤ (Fintype.card J : ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ Real.exp (-l*((Fintype.card J : ℝ)*t))*
        (∑ x : J → Ω, (∏ r, p (x r))*Real.exp (l*(∑ r, Y (x r)))) := hmarkov
    _ ≤ Real.exp (-l*((Fintype.card J : ℝ)*t))*
        Real.exp ((Fintype.card J : ℝ)*(8388608*l^2)) :=
      mul_le_mul_of_nonneg_left hbatch (Real.exp_pos _).le
    _ ≤ _ := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      by_cases ht1 : t ≤ 1
      · have hs : t^2 ≤ t := by nlinarith
        rw [min_eq_left hs]
        dsimp [l]
        rw [min_eq_left ht1]
        ring_nf
        exact le_rfl
      · have h1 : 1 ≤ t := le_of_not_ge ht1
        have hs : t ≤ t^2 := by nlinarith
        rw [min_eq_right hs]
        dsimp [l]
        rw [min_eq_right h1]
        nlinarith [mul_nonneg hM (sub_nonneg.mpr h1)]



end Section5FiniteProbability

end
set_option autoImplicit false
namespace Section5FiniteProbability
end Section5FiniteProbability
open Section5FiniteProbability
variable {Ω J : Type*} [Fintype Ω] [Fintype J] [DecidableEq J]
theorem solution (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (Y : Ω → ℝ)
    (hmgf : ∀ l : ℝ, |l| *512 ≤ 1/2 →
      (∑ x, p x*Real.exp (l*Y x)) ≤ Real.exp (8388608*l^2))
    (t : ℝ) (ht : 0 ≤ t) :
    (∑ x : J → Ω, if (Fintype.card J : ℝ)*t ≤ |∑ r, Y (x r)| then ∏ r, p (x r) else 0) ≤
      2*Real.exp (-(Fintype.card J : ℝ)*min (t^2) t/33554432) := by
  have hneg : ∀ l : ℝ, |l| *512 ≤ 1/2 →
      (∑ x, p x*Real.exp (l*(-Y x))) ≤ Real.exp (8388608*l^2) := by
    intro l hl
    have he := hmgf (-l) (by simpa only [abs_neg] using hl)
    simpa only [neg_mul,mul_neg,neg_sq] using he
  have hpt (x : J → Ω) :
      (if (Fintype.card J : ℝ)*t ≤ |∑ r, Y (x r)| then ∏ r, p (x r) else 0) ≤
      (if (Fintype.card J : ℝ)*t ≤ ∑ r, Y (x r) then ∏ r, p (x r) else 0)+
      (if (Fintype.card J : ℝ)*t ≤ ∑ r, -Y (x r) then ∏ r, p (x r) else 0) := by
    have hp0 : 0 ≤ ∏ r, p (x r) := Finset.prod_nonneg (fun r _ => hp (x r))
    rw [Finset.sum_neg_distrib]
    by_cases h : 0 ≤ ∑ r, Y (x r)
    · rw [abs_of_nonneg h]
      split_ifs <;> linarith
    · rw [abs_of_neg (lt_of_not_ge h)]
      split_ifs <;> linarith
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset (J → Ω))) => hpt x)
  rw [Finset.sum_add_distrib] at hsum
  linarith [Section5FiniteProbability.iid_subexponential_upper_tail (J := J) p hp Y hmgf t ht,
    Section5FiniteProbability.iid_subexponential_upper_tail (J := J) p hp (fun x => -Y x) hneg t ht]
