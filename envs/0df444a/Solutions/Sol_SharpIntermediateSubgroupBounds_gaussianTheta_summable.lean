-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.gaussianTheta_summable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:41:51.580699+00:00
-- url     : https://prove2.me/submissions/7ed5ce56-151a-4658-8e8c-33f32cd35827

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
theorem _root_.solution {p : ℝ} (hp : 1 < p) :
    Summable (fun z : ℤ ↦ Real.exp (-Real.log p * (z : ℝ) ^ 2)) :=
  summable_int_gaussian (Real.log_pos hp)
end SharpIntermediateSubgroupBounds
