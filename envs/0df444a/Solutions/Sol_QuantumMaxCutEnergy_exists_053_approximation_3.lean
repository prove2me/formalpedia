-- Prove2me | solution 3 for QuantumMaxCutEnergy.exists_053_approximation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T16:46:53.336864+00:00
-- url     : https://prove2.me/submissions/4e5ab652-eb3b-4c69-bdfc-1e95c9eaddfc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Theorems.Thm_QuantumMaxCutEnergy_agm_numeric_candidate_combination
import Theorems.Thm_QuantumMaxCutEnergy_agm_finite_product_estimator
import Theorems.Thm_QuantumMaxCutEnergy_polynomialTime_max_with_deterministic_estimator
import Theorems.Thm_QuantumMaxCutEnergy_agm_matching_forest_estimator_implementation
import Mathlib.Algebra.Order.BigOperators.Group.Finset
open scoped BigOperators

namespace QMC053

lemma const_le_average {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → ℝ) (c : ℝ) (h : ∀ i, c ≤ x i) :
    c ≤ (∑ i, x i) / (Fintype.card ι : ℝ) := by
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rw [le_div_iff₀ hcard]
  calc c * (Fintype.card ι : ℝ) = (Fintype.card ι : ℝ) * c := by ring
    _ = ∑ _i : ι, c := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ ∑ i, x i := Finset.sum_le_sum (fun i _ => h i)

lemma key_average (P : QuantumMaxCutEnergy.Algorithm) (b : QuantumMaxCutEnergy.Input → ℚ≥0)
    (G : QuantumMaxCutEnergy.Input)
    (hPavg : (0.953 : ℝ) * (QuantumMaxCutEnergy.optimum G + (∑ e, (G.weights e : ℝ))) / 3 ≤
      (∑ r : Fin (QuantumMaxCutEnergy.randomBits P G) → Bool, (P.run G (List.ofFn r) : ℝ)) /
        (Fintype.card (Fin (QuantumMaxCutEnergy.randomBits P G) → Bool) : ℝ))
    (hble : (b G : ℝ) ≤ QuantumMaxCutEnergy.optimum G)
    (m f : ℝ) (hfW : f ≤ ∑ e, (G.weights e : ℝ))
    (hupper : QuantumMaxCutEnergy.optimum G ≤ (∑ e, (G.weights e : ℝ)) + (m + f) / 2)
    (hfb : f ≤ (b G : ℝ))
    (hmatch : ((∑ e, (G.weights e : ℝ)) + 3 * m) / 2 ≤ (b G : ℝ)) :
    (0.53 : ℝ) * QuantumMaxCutEnergy.optimum G ≤
      (∑ r : Fin (QuantumMaxCutEnergy.randomBits P G) → Bool,
        ((max (b G) (P.run G (List.ofFn r)) : ℚ≥0) : ℝ)) /
        (Fintype.card (Fin (QuantumMaxCutEnergy.randomBits P G) → Bool) : ℝ) := by
  let W : ℝ := ∑ e, (G.weights e : ℝ)
  let O : ℝ := QuantumMaxCutEnergy.optimum G
  let N : ℕ := Fintype.card (Fin (QuantumMaxCutEnergy.randomBits P G) → Bool)
  let S : ℝ := ∑ r : Fin (QuantumMaxCutEnergy.randomBits P G) → Bool, (P.run G (List.ofFn r) : ℝ)
  let T : ℝ := ∑ r : Fin (QuantumMaxCutEnergy.randomBits P G) → Bool,
        ((max (b G) (P.run G (List.ofFn r)) : ℚ≥0) : ℝ)
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := Fintype.card_pos
    exact_mod_cast this
  have hptP : ∀ r : Fin (QuantumMaxCutEnergy.randomBits P G) → Bool,
      (P.run G (List.ofFn r) : ℝ) ≤ ((max (b G) (P.run G (List.ofFn r)) : ℚ≥0) : ℝ) := by
    intro r
    rw [NNRat.cast_max]
    exact le_max_right _ _
  have hptb : ∀ r : Fin (QuantumMaxCutEnergy.randomBits P G) → Bool,
      (b G : ℝ) ≤ ((max (b G) (P.run G (List.ofFn r)) : ℚ≥0) : ℝ) := by
    intro r
    rw [NNRat.cast_max]
    exact le_max_left _ _
  have hSleT : S ≤ T := Finset.sum_le_sum (fun r _ => hptP r)
  have hT0 : 0 ≤ T := Finset.sum_nonneg (fun r _ => NNRat.cast_nonneg _)
  have hbavg : (b G : ℝ) ≤ T / (N : ℝ) := const_le_average _ _ (fun r => hptb r)
  have hupperW : O ≤ W + (m + f) / 2 := hupper
  have hfW' : f ≤ W := hfW
  have hmatchW : (W + 3 * m) / 2 ≤ (b G : ℝ) := hmatch
  have hPavg' : (0.953 : ℝ) * (O + W) / 3 ≤ S / (N : ℝ) := hPavg
  have hSdivT : S / (N : ℝ) ≤ T / (N : ℝ) :=
    div_le_div_of_nonneg_right hSleT (le_of_lt hNpos)
  have hprod : (0.953 : ℝ) * (O + W) / 3 ≤ T / (N : ℝ) := le_trans hPavg' hSdivT
  have hforest : f ≤ T / (N : ℝ) := le_trans hfb hbavg
  have hmatching : (W + 3 * m) / 2 ≤ T / (N : ℝ) := le_trans hmatchW hbavg
  have hcomb := QuantumMaxCutEnergy.agm_numeric_candidate_combination
    (0.953 : ℝ) W m f O (T / (N : ℝ)) (by norm_num) hupperW hforest hmatching hprod
  have hE0 : 0 ≤ T / (N : ℝ) := div_nonneg hT0 (le_of_lt hNpos)
  linarith [hcomb, hE0]

end QMC053

open scoped BigOperators

theorem solution :
    ∃ A : QuantumMaxCutEnergy.Algorithm,
      QuantumMaxCutEnergy.PolynomialTime A ∧
      QuantumMaxCutEnergy.ApproximationRatio A (0.53 : ℝ) := by
  obtain ⟨P, hPpoly, hPbd⟩ := QuantumMaxCutEnergy.agm_finite_product_estimator
  obtain ⟨b, hbprog, hbbd⟩ := QuantumMaxCutEnergy.agm_matching_forest_estimator_implementation
  refine ⟨{ randomFactor := P.randomFactor
            randomDegree := P.randomDegree
            run := fun G r => max (b G) (P.run G r) }, ?_, ?_⟩
  · exact QuantumMaxCutEnergy.polynomialTime_max_with_deterministic_estimator P b hPpoly hbprog
  · intro G
    obtain ⟨hPle, hPavg⟩ := hPbd G
    obtain ⟨hble, m, f, hm0, hmf, hfW, hupper, hfb, hmatch⟩ := hbbd G
    refine ⟨?_, ?_⟩
    · intro r
      rw [NNRat.cast_max]
      exact max_le hble (hPle r)
    · simp only [QuantumMaxCutEnergy.randomBits]
      exact QMC053.key_average P b G hPavg hble m f hfW hupper hfb hmatch
