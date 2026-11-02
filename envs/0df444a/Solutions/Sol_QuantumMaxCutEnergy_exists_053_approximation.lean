-- Prove2me | solution 1 for QuantumMaxCutEnergy.exists_053_approximation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T14:32:04.963527+00:00
-- url     : https://prove2.me/submissions/cfa61864-11ac-472e-8d49-745f5d05525f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_QuantumMaxCutEnergy_agm_numeric_candidate_combination
import Theorems.Thm_QuantumMaxCutEnergy_agm_matching_forest_estimator_implementation
import Theorems.Thm_QuantumMaxCutEnergy_agm_finite_product_estimator
import Theorems.Thm_QuantumMaxCutEnergy_polynomialTime_max_with_deterministic_estimator
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open scoped BigOperators
open QuantumMaxCutEnergy

private theorem uniform_max_lower {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (b : ℚ≥0) (p : Ω → ℚ≥0) :
    (b : ℝ) ≤ (∑ r, ((max b (p r) : ℚ≥0) : ℝ)) / (Fintype.card Ω : ℝ) ∧
      (∑ r, (p r : ℝ)) / (Fintype.card Ω : ℝ) ≤
        (∑ r, ((max b (p r) : ℚ≥0) : ℝ)) / (Fintype.card Ω : ℝ) := by
  have hN : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  constructor
  · apply (le_div_iff₀ hN).2
    calc
      (b : ℝ) * (Fintype.card Ω : ℝ) = ∑ _r : Ω, (b : ℝ) := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun r _ => by exact_mod_cast le_max_left b (p r))
  · apply div_le_div_of_nonneg_right _ hN.le
    exact Finset.sum_le_sum (fun r _ => by exact_mod_cast le_max_right b (p r))

theorem agm_exists_of_implementations (α : ℝ) (hα : α ≤ (0.53 : ℝ)) :
    ∃ A : Algorithm, PolynomialTime A ∧ ApproximationRatio A α := by
  obtain ⟨b, hbtime, hb⟩ := agm_matching_forest_estimator_implementation
  obtain ⟨P, hPtime, hP⟩ := agm_finite_product_estimator
  let A : Algorithm :=
    { randomFactor := P.randomFactor
      randomDegree := P.randomDegree
      run := fun G r => max (b G) (P.run G r) }
  refine ⟨A, polynomialTime_max_with_deterministic_estimator P b hPtime hbtime, ?_⟩
  intro G
  obtain ⟨hbsound, m, f, _hm, _hmf, _hfW, hupper, hforest, hmatching⟩ := hb G
  have hmeans := uniform_max_lower (b G)
    (fun r : Fin (randomBits P G) → Bool => P.run G (List.ofFn r))
  have hcomb := agm_numeric_candidate_combination (0.953 : ℝ)
    (∑ e, (G.weights e : ℝ)) m f (optimum G) _ (by norm_num)
    hupper (hforest.trans hmeans.1) (hmatching.trans hmeans.1)
    ((hP G).2.trans hmeans.2)
  have hnonneg : (0 : ℝ) ≤ (b G : ℝ) := by exact_mod_cast (b G).property
  have hO : 0 ≤ optimum G := hnonneg.trans hbsound
  constructor
  · intro r
    change ((max (b G) (P.run G (List.ofFn r)) : ℚ≥0) : ℝ) ≤ optimum G
    rcases le_total (b G) (P.run G (List.ofFn r)) with h | h
    · rw [max_eq_right h]
      exact (hP G).1 r
    · rw [max_eq_left h]
      exact hbsound
  · change α * optimum G ≤
      (∑ r : Fin (randomBits P G) → Bool,
        ((max (b G) (P.run G (List.ofFn r)) : ℚ≥0) : ℝ)) /
        (Fintype.card (Fin (randomBits P G) → Bool) : ℝ)
    have hscaled := mul_le_mul_of_nonneg_right hα hO
    nlinarith only [hcomb, hscaled, hO]

theorem solution :
    ∃ A : Algorithm, PolynomialTime A ∧ ApproximationRatio A (0.53 : ℝ) :=
  agm_exists_of_implementations (0.53 : ℝ) (by norm_num)

#print axioms solution
