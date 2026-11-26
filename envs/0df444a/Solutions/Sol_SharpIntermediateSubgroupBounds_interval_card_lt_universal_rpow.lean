-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.interval_card_lt_universal_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:05:19.345229+00:00
-- url     : https://prove2.me/submissions/b58131c0-c4fc-440f-83aa-99de36e196f8

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
import Theorems.Thm_SharpIntermediateSubgroupBounds_sharpScale_eq_rpow
import Theorems.Thm_SharpIntermediateSubgroupBounds_interval_card_lt_universal

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
noncomputable section
universe u
variable {G : Type u} [Group G] [Fintype G]
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {H : Subgroup G} (hn : 1 < H.index) :
    (Nat.card (interval H) : ℝ) <
      sharpConstant 2 * (H.index : ℝ) ^ (indexLog 2 H.index / 4) := by
  rw [← sharpScale_eq_rpow (q := 2) (n := H.index) (by norm_num) (by omega)]
  exact interval_card_lt_universal hn
end SharpIntermediateSubgroupBounds
