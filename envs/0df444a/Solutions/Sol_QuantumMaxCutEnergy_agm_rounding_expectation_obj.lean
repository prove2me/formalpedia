-- Prove2me | solution 1 for QuantumMaxCutEnergy.agm_rounding_expectation_obj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T15:19:44.777069+00:00
-- url     : https://prove2.me/submissions/fe4fc895-a324-4b01-bd23-4a3621a33037

import Mathlib
import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEnergy_weightMatrix
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations

/-!
# Aggregating the rank-three rounding bound from pairs to the objective

`rank3_gaussian_rounding_distribution` gives a probability measure on unit vectors whose pair
means satisfy `E⟪r i, r j⟫ ≤ 0.046 + 0.954 X i j` for every pair. This file sums that bound
against the weights to obtain the objective-level statement

  `0.954 * obj X ≤ E[obj (gram r)]`.

The arithmetic is exact: `1 − 0.046 − 0.954 = 0`, so summing `1 − E⟪r i, r j⟫ ≥ 0.954 (1 − X i j)`
against the nonnegative weights leaves no residual constant.

Only the *double sum* form of the objective is used, so neither symmetry of `X` nor the edge
reindexing is needed: the pair bound holds for every ordered pair and the weights are nonnegative.
-/

open MeasureTheory Matrix
open scoped BigOperators

namespace QuantumMaxCutEnergy

/-- The weight matrix has nonnegative entries. -/
theorem weightMatrix_nonneg_proof (G : Input) (i j : Fin G.n) : 0 ≤ weightMatrix G i j := by
  by_cases hij : i < j
  · rw [weightMatrix_apply_of_lt hij]
    exact_mod_cast (G.weights ⟨(i, j), hij⟩).2
  · by_cases hji : j < i
    · rw [weightMatrix_apply_of_gt hji]
      exact_mod_cast (G.weights ⟨(j, i), hji⟩).2
    · have hEq : i = j := le_antisymm (not_lt.mp hji) (not_lt.mp hij)
      subst hEq
      rw [weightMatrix_apply_self]

/-- **The rounding bound at the level of the objective.** If a probability measure on `(ℝ³)ⁿ` has
pair means bounded by `0.046 + 0.954 X i j`, then the expected objective of the rounded point is at
least `0.954` times the objective of `X`. -/
theorem agm_rounding_expectation_obj_proof (G : Input) (X : Matrix (Fin G.n) (Fin G.n) ℝ)
    (μ : Measure (Fin G.n → Fin 3 → ℝ)) [IsProbabilityMeasure μ]
    (hint : ∀ i j : Fin G.n,
      Integrable (fun r : Fin G.n → Fin 3 → ℝ => ∑ a : Fin 3, r i a * r j a) μ)
    (hpair : ∀ i j, ∫ r, (∑ a : Fin 3, r i a * r j a) ∂μ ≤ 0.046 + 0.954 * X i j) :
    (0.954 : ℝ) * ModernConvex.Relaxations.maxcutRelaxationObjective (weightMatrix G) X
      ≤ ∫ r, ModernConvex.Relaxations.maxcutRelaxationObjective (weightMatrix G)
          (Matrix.of fun i j => ∑ a : Fin 3, r i a * r j a) ∂μ := by
  have hg : ∀ i j : Fin G.n,
      Integrable (fun r : Fin G.n → Fin 3 → ℝ => (1 : ℝ) - ∑ a : Fin 3, r i a * r j a) μ :=
    fun i j => (integrable_const 1).sub (hint i j)
  -- the value of the integral of the rounded objective
  have hval : (∫ r, ModernConvex.Relaxations.maxcutRelaxationObjective (weightMatrix G)
        (Matrix.of fun i j => ∑ a : Fin 3, r i a * r j a) ∂μ)
      = (1 / 4) * ∑ i, ∑ j,
          weightMatrix G i j * (1 - ∫ r, (∑ a : Fin 3, r i a * r j a) ∂μ) := by
    simp only [ModernConvex.Relaxations.maxcutRelaxationObjective, Matrix.of_apply]
    rw [integral_const_mul, integral_finset_sum]
    · congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finset_sum]
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_const_mul]
        congr 1
        rw [integral_sub (integrable_const 1) (hint i j), integral_const]
        simp
      · intro j _
        exact (hg i j).const_mul _
    · intro i _
      exact integrable_finset_sum _ fun j _ => (hg i j).const_mul _
  rw [hval]
  -- termwise comparison
  have hterm : ∀ i j : Fin G.n,
      weightMatrix G i j * (0.954 * (1 - X i j))
        ≤ weightMatrix G i j * (1 - ∫ r, (∑ a : Fin 3, r i a * r j a) ∂μ) := by
    intro i j
    refine mul_le_mul_of_nonneg_left ?_ (weightMatrix_nonneg_proof G i j)
    have h := hpair i j
    linarith
  have hstep : ∀ i : Fin G.n, (∑ j, weightMatrix G i j * (0.954 * (1 - X i j)))
      = 0.954 * ∑ j, weightMatrix G i j * (1 - X i j) := by
    intro i
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  calc (0.954 : ℝ) * ((1 / 4) * ∑ i, ∑ j, weightMatrix G i j * (1 - X i j))
      = (1 / 4) * ∑ i, (0.954 * ∑ j, weightMatrix G i j * (1 - X i j)) := by
        simp only [Finset.mul_sum]
        ring
    _ = (1 / 4) * ∑ i, ∑ j, weightMatrix G i j * (0.954 * (1 - X i j)) := by
        rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => (hstep i).symm]
    _ ≤ (1 / 4) * ∑ i, ∑ j,
          weightMatrix G i j * (1 - ∫ r, (∑ a : Fin 3, r i a * r j a) ∂μ) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j

end QuantumMaxCutEnergy

open QuantumMaxCutEnergy in
theorem solution (G : QuantumMaxCutEnergy.Input) (X : Matrix (Fin G.n) (Fin G.n) ℝ)
    (μ : Measure (Fin G.n → Fin 3 → ℝ)) [IsProbabilityMeasure μ]
    (hint : ∀ i j : Fin G.n,
      Integrable (fun r : Fin G.n → Fin 3 → ℝ => ∑ a : Fin 3, r i a * r j a) μ)
    (hpair : ∀ i j, ∫ r, (∑ a : Fin 3, r i a * r j a) ∂μ ≤ 0.046 + 0.954 * X i j) :
    (0.954 : ℝ) * ModernConvex.Relaxations.maxcutRelaxationObjective (weightMatrix G) X
      ≤ ∫ r, ModernConvex.Relaxations.maxcutRelaxationObjective (weightMatrix G)
          (Matrix.of fun i j => ∑ a : Fin 3, r i a * r j a) ∂μ :=
  QuantumMaxCutEnergy.agm_rounding_expectation_obj_proof G X μ hint hpair
