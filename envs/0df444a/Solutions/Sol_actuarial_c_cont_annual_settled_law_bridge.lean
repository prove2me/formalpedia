-- Prove2me | solution 1 for actuarial_c_cont_annual_settled_law_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-14T07:38:22.238413+00:00
-- url     : https://prove2.me/submissions/a05d4bcd-921c-43b2-be6e-496659be4b26

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_cont_annualSettlementPV
import Definitions.Def_actuarial_c_massPV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialAssurances.Continuous

open MeasureTheory

theorem solution (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (h : ℕ) (delta v : ℝ)
    (p : ℕ → ℝ)
    (hv : v = Real.exp (-delta))
    (hyears : ∀ j : ℕ, j < h →
      (μ (Set.Ico (j : ℝ) ((j + 1 : ℕ) : ℝ))).toReal = p j) :
    (∫ t, annualSettlementPV h delta t ∂μ) =
      ActuarialAssurances.massPV h v (fun _ => 1) p := by
  classical
  have hexp (k : ℕ) :
      Real.exp (-delta * (k : ℝ)) = (Real.exp (-delta))^k := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Nat.cast_succ, mul_add, Real.exp_add, ih, pow_succ]
        ring
  have hset (j : ℕ) :
      MeasurableSet (Set.Ico (j : ℝ) ((j + 1 : ℕ) : ℝ)) :=
    measurableSet_Ico
  have hf (j : ℕ) :
      (fun t : ℝ => if (j : ℝ) ≤ t ∧ t < ((j + 1 : ℕ) : ℝ)
        then Real.exp (-delta * ((j + 1 : ℕ) : ℝ)) else 0) =
      (Set.Ico (j : ℝ) ((j + 1 : ℕ) : ℝ)).indicator
        (fun _ : ℝ => Real.exp (-delta * ((j + 1 : ℕ) : ℝ))) := by
    funext t
    by_cases ht : (j : ℝ) ≤ t ∧ t < ((j + 1 : ℕ) : ℝ)
    · simp [Set.indicator, Set.mem_Ico, ht]
    · simp [Set.indicator, Set.mem_Ico, ht]
  have hint (j : ℕ) :
      Integrable (fun t : ℝ =>
        if (j : ℝ) ≤ t ∧ t < ((j + 1 : ℕ) : ℝ)
        then Real.exp (-delta * ((j + 1 : ℕ) : ℝ)) else 0) μ := by
    rw [hf j]
    exact (integrable_const _).indicator (hset j)
  unfold annualSettlementPV ActuarialAssurances.massPV
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [hf j]
    simp [integral_indicator_const, hset j,
      hyears j (Finset.mem_range.mp hj), hexp (j + 1), ← hv,
      mul_assoc, mul_comm, mul_left_comm]
    have hmass : μ.real (Set.Ico (j : ℝ) ((j : ℝ) + 1)) = p j := by
      have hjmass := hyears j (Finset.mem_range.mp hj)
      rw [measureReal_def]
      simpa only [Nat.cast_add, Nat.cast_one] using hjmass
    have hpow : Real.exp (-(delta * ((j : ℝ) + 1))) = v^(j + 1) := by
      have he : -(delta * ((j : ℝ) + 1)) =
          -delta * ((j + 1 : ℕ) : ℝ) := by
        push_cast
        ring
      rw [he, hexp (j + 1), ← hv]
    rw [hmass, hpow]
    ring
  · intro j hj
    exact hint j
