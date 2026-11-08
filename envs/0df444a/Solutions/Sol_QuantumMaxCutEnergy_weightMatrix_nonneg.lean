-- Prove2me | solution 1 for QuantumMaxCutEnergy.weightMatrix_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T15:19:44.251006+00:00
-- url     : https://prove2.me/submissions/28161185-0450-426e-80c8-47376f21a69b

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


end QuantumMaxCutEnergy

open QuantumMaxCutEnergy in
theorem solution (G : QuantumMaxCutEnergy.Input) (i j : Fin G.n) :
    0 ≤ weightMatrix G i j :=
  QuantumMaxCutEnergy.weightMatrix_nonneg_proof G i j
