-- Prove2me | solution 1 for Paper.Hypergraph.vertexMultiplier_integral_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:19:19.488389+00:00
-- url     : https://prove2.me/submissions/89d4d35c-88cf-4507-b5eb-ed3e0ae6a7bd

import Definitions.Def_Paper_RoundingAveraging
import Definitions.Def_Paper_RoundingDegeneracy
import Theorems.Thm_Paper_Hypergraph_levelMeasure_Icc_le


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset MeasureTheory
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution {x d : ℕ → ℝ} {v : ℕ} (hx : 0 ≤ x v) :
    ∫ r, vertexMultiplier x d v r ∂levelMeasure ≤ 1 := by
  by_cases h0 : x v = 0
  · simp [vertexMultiplier, h0]
  have hp : 0 < x v := lt_of_le_of_ne hx (Ne.symm h0)
  rw [vertexMultiplier, integral_indicator_const _ measurableSet_Icc]
  change levelMeasure.real (Set.Icc (d v - x v) (d v)) * (1 / x v) ≤ 1
  have h := levelMeasure_Icc_le (d v - x v) (d v)
  have heq : max (d v - (d v - x v)) 0 = x v := by rw [sub_sub_cancel, max_eq_left hx]
  rw [heq] at h
  calc
    _ ≤ x v * (1 / x v) := mul_le_mul_of_nonneg_right h (by positivity)
    _ = 1 := by field_simp
end Paper.Hypergraph
