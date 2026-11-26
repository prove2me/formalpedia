-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.interval_card_lt_universal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:04:30.638813+00:00
-- url     : https://prove2.me/submissions/91ed33d4-0471-4e4c-a6c8-08f7ffa49f81

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
      sharpConstant 2 * sharpScale 2 H.index := by
  have hp : H.index.minFac.Prime := Nat.minFac_prime (by omega)
  exact interval_card_lt_sharpConstant hn (by norm_num) hp.two_le
end SharpIntermediateSubgroupBounds
