-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.interval_card_lt_leastPrime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:04:30.040682+00:00
-- url     : https://prove2.me/submissions/f5695589-a8a1-4254-bd54-aabbb1912de3

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
import Theorems.Thm_SharpIntermediateSubgroupBounds_interval_card_lt_sharpConstant

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
noncomputable section
universe u
variable {G : Type u} [Group G] [Fintype G]
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {H : Subgroup G} (hn : 1 < H.index) :
    (Nat.card (interval H) : ℝ) <
      sharpConstant (H.index.minFac : ℝ) *
        sharpScale H.index.minFac H.index := by
  have hp : H.index.minFac.Prime := Nat.minFac_prime (by omega)
  exact interval_card_lt_sharpConstant hn hp.one_lt le_rfl
end SharpIntermediateSubgroupBounds
