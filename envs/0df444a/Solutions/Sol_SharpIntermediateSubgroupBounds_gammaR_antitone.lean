-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.gammaR_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:54:19.01475+00:00
-- url     : https://prove2.me/submissions/2bc4d7c3-8347-4bf9-a214-4e7d99d72a6b

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Theorems.Thm_SharpIntermediateSubgroupBounds_gammaR_succ
import Theorems.Thm_SharpIntermediateSubgroupBounds_gammaR_pos

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p : ℝ} (hp : 1 < p) : Antitone (gammaR p) := by
  apply antitone_nat_of_succ_le
  intro r
  rw [gammaR_succ]
  apply mul_le_of_le_one_right (gammaR_pos hp r).le
  have hp0 : 0 < p := lt_trans (by norm_num) hp
  exact sub_le_self 1 (pow_nonneg (inv_pos.mpr hp0).le _)
end SharpIntermediateSubgroupBounds
