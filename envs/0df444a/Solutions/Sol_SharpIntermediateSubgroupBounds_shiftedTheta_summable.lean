-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.shiftedTheta_summable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:41:50.625858+00:00
-- url     : https://prove2.me/submissions/815a2447-4476-40ff-8468-86a9c2e0c22e

import Definitions.Def_SharpIntermediateSubgroupBounds_Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Theorems.Thm_SharpIntermediateSubgroupBounds_summable_int_gaussian

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p x : ℝ} (hp : 1 < p) :
    Summable (fun z : ℤ ↦ Real.exp (-Real.log p * ((z : ℝ) - x) ^ 2)) := by
  let A := Real.log p
  have hA : 0 < A := Real.log_pos hp
  have hbase := summable_int_gaussian (A := A / 2) (by positivity)
  have hmajor := hbase.mul_left (Real.exp (A * x ^ 2))
  refine hmajor.of_norm_bounded (fun z ↦ ?_)
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [← Real.exp_add]
  rw [Real.exp_le_exp]
  have hs : 0 ≤ ((z : ℝ) - 2 * x) ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg hA.le hs]
end SharpIntermediateSubgroupBounds
