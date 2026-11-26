-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.gammaR_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:47:03.895806+00:00
-- url     : https://prove2.me/submissions/7ea4be60-3d6d-45b2-9825-29016ce6884a

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
theorem _root_.solution {p : ℝ} (hp : 1 < p) (r : ℕ) : gammaR p r ≤ 1 := by
  have hp0 : 0 < p := lt_trans (by norm_num) hp
  rw [gammaR]
  apply Finset.prod_le_one
  · intro j hj
    exact (sub_pos.mpr <| pow_lt_one₀ (inv_pos.mpr hp0).le
      (inv_lt_one_of_one_lt₀ hp) (by omega)).le
  · intro j hj
    have : 0 ≤ p⁻¹ ^ (j + 1) := pow_nonneg (inv_pos.mpr hp0).le _
    linarith
end SharpIntermediateSubgroupBounds
