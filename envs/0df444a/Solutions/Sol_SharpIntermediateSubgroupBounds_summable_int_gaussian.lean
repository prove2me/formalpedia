-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.summable_int_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:41:10.760826+00:00
-- url     : https://prove2.me/submissions/3c55096c-bedf-4478-ac49-fe7bf80f0b37

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

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {A : ℝ} (hA : 0 < A) :
    Summable (fun z : ℤ ↦ Real.exp (-A * (z : ℝ) ^ 2)) := by
  have hT : 0 < A / Real.pi := div_pos hA Real.pi_pos
  have h := summable_pow_mul_jacobiTheta₂_term_bound 0 hT 0
  simpa only [pow_zero, Int.cast_one, one_mul, mul_zero, sub_zero] using h.congr
    (fun z ↦ by
      congr 1
      field_simp [Real.pi_ne_zero]
      ring)
end SharpIntermediateSubgroupBounds
