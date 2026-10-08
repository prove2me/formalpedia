-- Prove2me | solution 1 for QueueingFundamentals.GM1.beta_eq_lst
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T00:31:55.80872+00:00
-- url     : https://prove2.me/submissions/0e8607d9-f0a8-44e8-82ae-8f87386a6cf7

import Mathlib
import Definitions.Def_QueueingFundamentals_GM1_EmbeddedChain

set_option autoImplicit false

open MeasureTheory in
theorem GM1beta_aux_real_hasSum (x : ℝ) :
    HasSum (fun n : ℕ => Real.exp (-x) * x ^ n / (Nat.factorial n : ℝ)) 1 := by
  have h := (NormedSpace.expSeries_div_hasSum_exp (x : ℝ)).mul_left (Real.exp (-x))
  rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  refine h.congr_fun ?_
  intro n
  simp only [mul_div_assoc]

theorem GM1beta_aux_complex_hasSum (mu t : ℝ) (z : ℂ) :
    HasSum (fun n : ℕ => ((Real.exp (-mu * t) * (mu * t) ^ n / (Nat.factorial n : ℝ) : ℝ) : ℂ) * z ^ n)
      (Complex.exp (-((mu : ℂ) * (1 - z)) * (t : ℂ))) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp ((mu : ℂ) * t * z)).mul_left
    ((Real.exp (-mu * t) : ℝ) : ℂ)
  rw [← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp, ← Complex.exp_add] at h
  have e : -((mu : ℂ) * (1 - z)) * (t : ℂ) = ((-mu * t : ℝ) : ℂ) + (mu : ℂ) * t * z := by
    push_cast; ring
  rw [e]
  refine h.congr_fun ?_
  intro n
  push_cast
  rw [mul_pow, mul_pow]
  ring

open MeasureTheory in
theorem GM1beta_aux_integral (A : Measure ℝ) (mu : ℝ) (n : ℕ) (z : ℂ) :
    (QueueingFundamentals.GM1.serviceProb A mu n : ℂ) * z ^ n =
      ∫ t in Set.Ici (0 : ℝ),
        ((Real.exp (-mu * t) * (mu * t) ^ n / (Nat.factorial n : ℝ) : ℝ) : ℂ) * z ^ n ∂A := by
  rw [integral_mul_const, integral_complex_ofReal]
  rfl

open MeasureTheory in
theorem QueueingFundamentals.GM1.beta_eq_lst_sol (A : Measure ℝ) (lam mu : ℝ) (hlam : 0 < lam)
    (hmu : 0 < mu) (hA : QueueingFundamentals.GM1.IsInterarrivalLaw A lam) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    HasSum (fun n : ℕ => (QueueingFundamentals.GM1.serviceProb A mu n : ℂ) * z ^ n)
      (QueueingFundamentals.GM1.lst A ((mu : ℂ) * (1 - z))) := by
  have := hA.isProbability
  simp_rw [GM1beta_aux_integral]
  unfold QueueingFundamentals.GM1.lst
  refine hasSum_integral_of_dominated_convergence
    (fun n t => Real.exp (-mu * t) * (mu * t) ^ n / (Nat.factorial n : ℝ)) ?_ ?_ ?_ ?_ ?_
  · intro n
    exact (by fun_prop : Continuous fun t : ℝ =>
      ((Real.exp (-mu * t) * (mu * t) ^ n / (Nat.factorial n : ℝ) : ℝ) : ℂ) * z ^ n).aestronglyMeasurable
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    have ht : (0 : ℝ) ≤ t := ht
    rw [norm_mul, Complex.norm_real, norm_pow, Real.norm_of_nonneg (by positivity)]
    have : ‖z‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg _) hz
    have h0 : 0 ≤ Real.exp (-mu * t) * (mu * t) ^ n / (Nat.factorial n : ℝ) := by positivity
    calc _ ≤ Real.exp (-mu * t) * (mu * t) ^ n / (Nat.factorial n : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left this h0
      _ = _ := mul_one _
  · exact Filter.Eventually.of_forall fun t => by
      have := GM1beta_aux_real_hasSum (mu * t)
      simp only [neg_mul] at this ⊢
      exact this.summable
  · have : (fun t : ℝ => ∑' n : ℕ, Real.exp (-mu * t) * (mu * t) ^ n / (Nat.factorial n : ℝ))
        = fun _ => (1 : ℝ) := by
      funext t
      have := GM1beta_aux_real_hasSum (mu * t)
      simp only [neg_mul] at this ⊢
      exact this.tsum_eq
    rw [this]
    exact integrable_const _
  · exact Filter.Eventually.of_forall fun t => GM1beta_aux_complex_hasSum mu t z

open MeasureTheory QueueingFundamentals.GM1 in
theorem solution (A : Measure ℝ) (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hA : IsInterarrivalLaw A lam) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    HasSum (fun n : ℕ => (serviceProb A mu n : ℂ) * z ^ n) (lst A ((mu : ℂ) * (1 - z))) := by
  exact QueueingFundamentals.GM1.beta_eq_lst_sol A lam mu hlam hmu hA z hz
