-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P31.power_law_density_moments
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:29:54.026749+00:00
-- url     : https://prove2.me/submissions/be5a1d50-a42a-4acd-8fba-5c22d3fababa

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P31

open MeasureTheory
open QAlgorithms.Papers.Independent.Advance50.P31

theorem s110_pl_int (A s r : ℝ) (hs : -1 < s) (hr : 0 < r) :
    IntegrableOn (fun e : ℝ => A * (e ^ s * Real.exp (-(r * e)))) (Set.Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) hs one_pos hr
  have : (fun x : ℝ => x ^ s * Real.exp (-r * x ^ (1:ℝ))) = fun e => e ^ s * Real.exp (-(r * e)) := by
    funext x; rw [Real.rpow_one, neg_mul]
  rw [this] at h
  exact h.const_mul A

theorem s110_pl_eq1 (A a beta : ℝ) (k : ℕ) :
    Set.EqOn (fun e => densityOfStates A a e * Real.exp (-(k : ℝ) * beta * e))
      (fun e => A * (e ^ (a - 1) * Real.exp (-((k * beta) * e)))) (Set.Ioi 0) := by
  intro e _
  simp only [densityOfStates]
  rw [neg_mul, neg_mul]; ring

theorem s110_pl_eq2 (A a beta : ℝ) (k : ℕ) :
    Set.EqOn (fun e => beta * e * densityOfStates A a e * Real.exp (-(k : ℝ) * beta * e))
      (fun e => (A * beta) * (e ^ ((a + 1) - 1) * Real.exp (-((k * beta) * e)))) (Set.Ioi 0) := by
  intro e he
  have he' : 0 < e := he
  simp only [densityOfStates]
  rw [show a + 1 - 1 = (a - 1) + 1 by ring, Real.rpow_add_one he'.ne', neg_mul, neg_mul]
  ring

theorem solution
    (A a beta : ℝ) (hA : 0 < A) (ha : 0 < a) (hbeta : 0 < beta) :
    (∀ k : ℕ, 0 < k →
      IntegrableOn (fun e => densityOfStates A a e *
        Real.exp (-(k : ℝ) * beta * e)) (Set.Ioi (0 : ℝ)) ∧
      IntegrableOn (fun e => beta * e * densityOfStates A a e *
        Real.exp (-(k : ℝ) * beta * e)) (Set.Ioi (0 : ℝ)) ∧
      boltzmannMoment A a beta k = A * Real.Gamma a / ((k : ℝ) * beta) ^ a ∧
      weightedMoment A a beta k / boltzmannMoment A a beta k = a / (k : ℝ)) ∧
    (1 < a → boltzmannMoment A a beta 2 * (1 - a) / 2 < 0) := by
  have hB : ∀ k : ℕ, 0 < k → boltzmannMoment A a beta k = A * Real.Gamma a / ((k : ℝ) * beta) ^ a := by
    intro k hk
    have hr : 0 < (k : ℝ) * beta := mul_pos (by exact_mod_cast hk) hbeta
    unfold boltzmannMoment
    rw [setIntegral_congr_fun measurableSet_Ioi (s110_pl_eq1 A a beta k), integral_const_mul,
      Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr, Real.div_rpow zero_le_one hr.le, Real.one_rpow]
    ring
  refine ⟨fun k hk => ?_, fun ha1 => ?_⟩
  · have hr : 0 < (k : ℝ) * beta := mul_pos (by exact_mod_cast hk) hbeta
    refine ⟨?_, ?_, hB k hk, ?_⟩
    · exact (s110_pl_int A (a - 1) _ (by linarith) hr).congr_fun (s110_pl_eq1 A a beta k).symm measurableSet_Ioi
    · exact (s110_pl_int (A * beta) ((a + 1) - 1) _ (by linarith) hr).congr_fun
        (s110_pl_eq2 A a beta k).symm measurableSet_Ioi
    · rw [hB k hk]
      unfold weightedMoment
      rw [setIntegral_congr_fun measurableSet_Ioi (s110_pl_eq2 A a beta k), integral_const_mul,
        Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith) hr, Real.div_rpow zero_le_one hr.le,
        Real.one_rpow, Real.Gamma_add_one ha.ne', Real.rpow_add_one hr.ne']
      have hk' : (0:ℝ) < k := by exact_mod_cast hk
      have hG : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
      have hp : 0 < ((k:ℝ) * beta) ^ a := Real.rpow_pos_of_pos hr a
      field_simp
  · rw [hB 2 two_pos]
    have hG : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
    have hp : 0 < ((2:ℕ) * beta : ℝ) ^ a := Real.rpow_pos_of_pos (by positivity) a
    have : 0 < A * Real.Gamma a / (((2:ℕ):ℝ) * beta) ^ a := by positivity
    have h2 : 1 - a < 0 := by linarith
    nlinarith
