-- Prove2me | solution 1 for SuttonBartoRL.Bandit.performance_gradient_eq_expectation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:19:58.559374+00:00
-- url     : https://prove2.me/submissions/de91ab57-8cd8-403d-90b1-7679c95a778e

import Mathlib
import Definitions.Def_SuttonBartoRL_Bandit_GradientBandit

open SuttonBartoRL.Bandit in
theorem pg_c8118741_partial {k : ℕ} (H qstar : Fin k → ℝ) (a : Fin k) :
    partialDeriv (expectedReward qstar) H a =
      (Real.exp (H a) * qstar a * (∑ b, Real.exp (H b))
        - (∑ x, Real.exp (H x) * qstar x) * Real.exp (H a)) / (∑ b, Real.exp (H b)) ^ 2 := by
  unfold partialDeriv
  have hu : ∀ x, HasDerivAt (fun h => Function.update H a h x) (if x = a then 1 else 0) (H a) := by
    intro x
    by_cases hx : x = a
    · subst hx
      simp only [Function.update_self, if_true]
      exact hasDerivAt_id _
    · simp only [Function.update_of_ne hx, hx, if_false]
      exact hasDerivAt_const _ _
  have he : ∀ x, HasDerivAt (fun h => Real.exp (Function.update H a h x))
      (Real.exp (H x) * (if x = a then 1 else 0)) (H a) := by
    intro x
    have := (hu x).exp
    rwa [Function.update_eq_self] at this
  have hS : HasDerivAt (fun h => ∑ b, Real.exp (Function.update H a h b))
      (∑ b, Real.exp (H b) * (if b = a then 1 else 0)) (H a) :=
    HasDerivAt.fun_sum (fun b _ => he b)
  have hN : HasDerivAt (fun h => ∑ x, Real.exp (Function.update H a h x) * qstar x)
      (∑ x, Real.exp (H x) * (if x = a then 1 else 0) * qstar x) (H a) :=
    HasDerivAt.fun_sum (fun x _ => (he x).mul_const (qstar x))
  have hpos : (∑ b, Real.exp (Function.update H a (H a) b)) ≠ 0 :=
    (Finset.sum_pos (fun b _ => Real.exp_pos _) ⟨a, Finset.mem_univ _⟩).ne'
  have hD := hN.div hS hpos
  have hfun : (fun h => expectedReward qstar (Function.update H a h)) =
      fun h => (∑ x, Real.exp (Function.update H a h x) * qstar x) /
        ∑ b, Real.exp (Function.update H a h b) := by
    funext h
    unfold expectedReward softmaxPolicy
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    ring
  rw [hfun]
  refine hD.deriv.trans ?_
  simp only [Function.update_eq_self, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

open SuttonBartoRL.Bandit in
theorem pg_c8118741_integral {k : ℕ} (qstar : Fin k → ℝ)
    (ν : Fin k → MeasureTheory.Measure ℝ) [∀ x, MeasureTheory.IsProbabilityMeasure (ν x)]
    (hint : ∀ x, MeasureTheory.Integrable (fun r : ℝ => r) (ν x))
    (hmean : ∀ x, ∫ r, r ∂(ν x) = qstar x) (B c : ℝ) (x : Fin k) :
    ∫ r, (r - B) * c ∂(ν x) = (qstar x - B) * c := by
  have hf : (fun r : ℝ => (r - B) * c) = fun r => c * r + (-(B * c)) := by
    funext r; ring
  rw [hf, MeasureTheory.integral_add ((hint x).const_mul _) (MeasureTheory.integrable_const _),
    MeasureTheory.integral_const, MeasureTheory.integral_const_mul, hmean x]
  simp only [MeasureTheory.probReal_univ, one_smul]
  ring

open SuttonBartoRL.Bandit in
theorem solution {k : ℕ} (H qstar : Fin k → ℝ)
    (ν : Fin k → MeasureTheory.Measure ℝ) [∀ x, MeasureTheory.IsProbabilityMeasure (ν x)]
    (hint : ∀ x, MeasureTheory.Integrable (fun r : ℝ => r) (ν x))
    (hmean : ∀ x, ∫ r, r ∂(ν x) = qstar x) (B : ℝ) (a : Fin k) :
    partialDeriv (expectedReward qstar) H a
      = ∑ x, softmaxPolicy H x *
          ∫ r, (r - B) * ((if a = x then 1 else 0) - softmaxPolicy H a) ∂(ν x) := by
  simp only [pg_c8118741_integral qstar ν hint hmean B, pg_c8118741_partial]
  have hS : (∑ b, Real.exp (H b)) ≠ 0 :=
    (Finset.sum_pos (fun b _ => Real.exp_pos _) ⟨a, Finset.mem_univ _⟩).ne'
  set S := ∑ b, Real.exp (H b) with hSdef
  set N := ∑ x, Real.exp (H x) * qstar x with hNdef
  have key : ∑ x, softmaxPolicy H x *
      ((qstar x - B) * ((if a = x then 1 else 0) - softmaxPolicy H a))
      = ∑ x, ((- (Real.exp (H a) / S) * (Real.exp (H x) * qstar x)
          + (Real.exp (H a) / S) * B * Real.exp (H x)) / S
          + (if a = x then Real.exp (H x) * (qstar x - B) / S else 0)) := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    unfold softmaxPolicy
    rw [← hSdef]
    split_ifs <;> ring
  rw [key, Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos (Finset.mem_univ _),
    ← Finset.sum_div, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← hSdef, ← hNdef]
  field_simp
  ring
