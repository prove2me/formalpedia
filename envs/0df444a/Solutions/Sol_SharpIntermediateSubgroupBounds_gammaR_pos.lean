-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.gammaR_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:41:44.642232+00:00
-- url     : https://prove2.me/submissions/2c270c66-5904-4f4d-b07e-e032dea0bd23

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
theorem _root_.solution {p : ℝ} (hp : 1 < p) (r : ℕ) : 0 < gammaR p r := by
  rw [gammaR]
  apply Finset.prod_pos
  intro j hj
  have hp0 : 0 < p := lt_trans (by norm_num) hp
  have hinv : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
  exact sub_pos.mpr (pow_lt_one₀ (inv_pos.mpr hp0).le hinv (by omega))
end SharpIntermediateSubgroupBounds
