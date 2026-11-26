-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.interval_card_lt_leastPrime_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:05:19.717207+00:00
-- url     : https://prove2.me/submissions/f1f03e21-64e9-4e58-8742-ba6a60bc38e8

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
import Theorems.Thm_SharpIntermediateSubgroupBounds_interval_card_lt_leastPrime

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
        (H.index : ℝ) ^
          (indexLog H.index.minFac H.index / 4) := by
  have hp : H.index.minFac.Prime := Nat.minFac_prime (by omega)
  rw [← sharpScale_eq_rpow hp.one_lt (by omega)]
  exact interval_card_lt_leastPrime hn
end SharpIntermediateSubgroupBounds
