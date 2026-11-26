-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.summable_nat_odd_gaussian_inv_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:55:07.051394+00:00
-- url     : https://prove2.me/submissions/e1f4f0bb-79e0-4691-be03-5fee3aeb4767

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
    Summable (fun j : ℕ ↦ (p : ℝ)⁻¹ ^ (j * (j + 1))) := by
  have hpR0 : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
  have hpR1 : (p : ℝ)⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ (by exact_mod_cast (by omega : 1 < p))
  have hgeom : Summable (fun j : ℕ ↦ (p : ℝ)⁻¹ ^ j) :=
    summable_geometric_of_lt_one hpR0 hpR1
  exact hgeom.of_nonneg_of_le (fun j ↦ pow_nonneg hpR0 _)
    (fun j ↦ pow_le_pow_of_le_one hpR0 hpR1.le (by
      calc
        j = j * 1 := by simp
        _ ≤ j * (j + 1) :=
          Nat.mul_le_mul_left j (Nat.succ_le_succ (Nat.zero_le j))))
end SharpIntermediateSubgroupBounds
