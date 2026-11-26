-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.interval_card_lt_universal_decimal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:06:18.670104+00:00
-- url     : https://prove2.me/submissions/1f248f83-3429-449a-b5f6-8df6d12710e8

import Definitions.Def_SharpIntermediateSubgroupBounds_Packing
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Definitions.Def_SharpIntermediateSubgroupBounds_Decimal
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_GroupMain
import Theorems.Thm_SharpIntermediateSubgroupBounds_interval_card_lt_universal_rpow
import Theorems.Thm_SharpIntermediateSubgroupBounds_sharpConstant_two_lt_decimal


set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
noncomputable section
universe u
variable {G : Type u} [Group G] [Fintype G]
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {H : Subgroup G} (hn : 1 < H.index) :
    (Nat.card (interval H) : ℝ) <
      ((3685984401 : ℝ) / 500000000) *
        (H.index : ℝ) ^ (indexLog 2 H.index / 4) := by
  have hscale : 0 < (H.index : ℝ) ^ (indexLog 2 H.index / 4) := by positivity
  exact (interval_card_lt_universal_rpow hn).trans
    (mul_lt_mul_of_pos_right sharpConstant_two_lt_decimal hscale)
end SharpIntermediateSubgroupBounds
