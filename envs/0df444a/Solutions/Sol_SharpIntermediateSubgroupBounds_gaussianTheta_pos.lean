-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.gaussianTheta_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:42:41.936699+00:00
-- url     : https://prove2.me/submissions/97acbcd7-bf75-48a9-a3f5-2e197b12b953

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
theorem _root_.solution {p : ℝ} (hp : 1 < p) : 0 < gaussianTheta p := by
  unfold gaussianTheta
  apply (gaussianTheta_summable hp).tsum_pos (fun z ↦ (Real.exp_pos _).le) 0
  simpa using Real.exp_pos (0 : ℝ)
end SharpIntermediateSubgroupBounds
