-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.shiftedTheta_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:03:46.607993+00:00
-- url     : https://prove2.me/submissions/23995f3d-232e-46dd-9dd3-7d1106625064

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
import Theorems.Thm_SharpIntermediateSubgroupBounds_shiftedTheta_lt_of_not_integer
import Theorems.Thm_SharpIntermediateSubgroupBounds_shiftedTheta_eq_of_integer

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p x : ℝ} (hp : 1 < p) :
    shiftedTheta p x = gaussianTheta p ↔ ∃ z : ℤ, (z : ℝ) = x := by
  constructor
  · intro h
    by_contra hx
    exact (shiftedTheta_lt_of_not_integer hp hx).ne h
  · exact shiftedTheta_eq_of_integer hp
end SharpIntermediateSubgroupBounds
