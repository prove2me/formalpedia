-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.gaussianTheta_eq_one_add_two_mul_tsum_pnat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:53:27.518911+00:00
-- url     : https://prove2.me/submissions/064fe4e4-24be-4779-bb63-dd2b4b7747d2

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
import Theorems.Thm_SharpIntermediateSubgroupBounds_gaussianTheta_summable

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p : ℝ} (hp : 1 < p) :
    gaussianTheta p = 1 + 2 * ∑' j : ℕ+,
      Real.exp (-Real.log p * (j : ℝ) ^ 2) := by
  unfold gaussianTheta
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat]
  · simp
  · intro z
    simp
  · exact gaussianTheta_summable hp
end SharpIntermediateSubgroupBounds
