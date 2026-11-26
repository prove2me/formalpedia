-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.eulerC_partial_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:54:46.728801+00:00
-- url     : https://prove2.me/submissions/40187cd0-ba2b-480f-883f-862da940b925

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
import Theorems.Thm_SharpIntermediateSubgroupBounds_multipliable_euler_factors

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p : ℝ} (hp : 2 ≤ p) :
    Tendsto (fun r : ℕ ↦ ∏ n ∈ Finset.range r, (1 - p⁻¹ ^ (n + 1))⁻¹)
      atTop (nhds (eulerC p)) := by
  exact (multipliable_euler_factors hp).tendsto_prod_tprod_nat
end SharpIntermediateSubgroupBounds
