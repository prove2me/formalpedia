-- Prove2me | solution 1 for ThreeSum.LocalCoverBounds.degree_sq_lt_output_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:16:21.851734+00:00
-- url     : https://prove2.me/submissions/1598ac2e-c936-4d40-988e-853396df7801

import Definitions.Def_Submission_ThreeSum_LayerCounts
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Sqrt
import Mathlib.NumberTheory.Bertrand
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Theorems.Thm_ThreeSum_LocalCoverBounds_degree_le_vertices
import Theorems.Thm_ThreeSum_LocalCoverBounds_vertices_mul_degree
import Theorems.Thm_ThreeSum_LocalCoverBounds_groupSize_lt_pow

set_option autoImplicit false
open ThreeSum ThreeSum.LocalCoverBounds
open scoped BigOperators
namespace ThreeSum.LocalCoverBounds
theorem _root_.solution {L h : ℕ} (hh : 0 < h) (hL : 2 * h ≤ L) :
    degree L h ^ 2 < outputCount L h * 2 ^ (2 * h) := by
  have hM : 0 < outputCount L h := Nat.choose_pos hL
  calc
    degree L h ^ 2 = degree L h * degree L h := by rw [pow_two]
    _ ≤ vertexCount L h * degree L h :=
      Nat.mul_le_mul_right _ (degree_le_vertices L h)
    _ = outputCount L h * groupSize h := vertices_mul_degree L h
    _ < outputCount L h * 2 ^ (2 * h) :=
      Nat.mul_lt_mul_of_pos_left (groupSize_lt_pow hh) hM
end ThreeSum.LocalCoverBounds
