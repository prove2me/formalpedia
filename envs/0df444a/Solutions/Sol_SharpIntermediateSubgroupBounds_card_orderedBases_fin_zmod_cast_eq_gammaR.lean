-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.card_orderedBases_fin_zmod_cast_eq_gammaR
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:55:47.830148+00:00
-- url     : https://prove2.me/submissions/bfe12fe2-8389-454a-a9f8-422eabf94808

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Theorems.Thm_SharpIntermediateSubgroupBounds_frameProd_diagonal_cast_real_eq_gammaR
import Theorems.Thm_SharpIntermediateSubgroupBounds_card_orderedBases_fin_zmod


set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution (p r : ℕ) [Fact p.Prime] :
    (Nat.card (LinearIndependentFrames (ZMod p) (Fin r → ZMod p) r) : ℝ) =
      (p : ℝ) ^ (r * r) * gammaR (p : ℝ) r := by
  rw [card_orderedBases_fin_zmod]
  exact frameProd_diagonal_cast_real_eq_gammaR (Nat.Prime.two_le (Fact.out : p.Prime))
end SharpIntermediateSubgroupBounds
