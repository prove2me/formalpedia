-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.summable_nat_gaussian_inv_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:43:20.341475+00:00
-- url     : https://prove2.me/submissions/bca4fcba-bdd7-44cb-bdf8-1a38d646ac48

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) :
    Summable (fun j : ℕ ↦ (p : ℝ)⁻¹ ^ (j * j)) := by
  have hpR0 : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
  have hpR1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (by omega : 1 < p))
  have hgeom : Summable (fun j : ℕ ↦ (p : ℝ)⁻¹ ^ j) :=
    summable_geometric_of_lt_one hpR0 hpR1
  exact hgeom.of_nonneg_of_le (fun j ↦ pow_nonneg hpR0 _)
    (fun j ↦ pow_le_pow_of_le_one hpR0 hpR1.le (Nat.le_mul_self j))
end SharpIntermediateSubgroupBounds
