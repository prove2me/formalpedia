-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.card_generatingFrames_fin_zmod_cast_eq_gammaR
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:56:37.528202+00:00
-- url     : https://prove2.me/submissions/ec559e34-ee2c-4f6b-a866-61a38205b600

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Theorems.Thm_SharpIntermediateSubgroupBounds_card_orderedBases_fin_zmod_cast_eq_gammaR

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution (p r : ℕ) [Fact p.Prime] :
    (Nat.card (GeneratingFramesFinZMod p r) : ℝ) =
      (p : ℝ) ^ (r * r) * gammaR (p : ℝ) r := by
  rw [Nat.card_congr (generatingFramesEquivOrderedBasesFinZMod p r)]
  exact card_orderedBases_fin_zmod_cast_eq_gammaR p r
end SharpIntermediateSubgroupBounds
