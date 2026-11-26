-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.interval_card_lt_sharpConstant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:03:30.95561+00:00
-- url     : https://prove2.me/submissions/58e50558-5f9d-415d-a7dc-85aad6569ca3

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
import Theorems.Thm_SharpIntermediateSubgroupBounds_indexLog_nonneg
import Theorems.Thm_SharpIntermediateSubgroupBounds_interval_card_le_finiteThetaSum
import Theorems.Thm_SharpIntermediateSubgroupBounds_finiteThetaSum_lt


set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
noncomputable section
universe u
variable {G : Type u} [Group G] [Fintype G]
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {H : Subgroup G} (hn : 1 < H.index)
    {q : ℕ} (hq : 1 < q) (hqp : q ≤ H.index.minFac) :
    (Nat.card (interval H) : ℝ) <
      sharpConstant (q : ℝ) * sharpScale q H.index := by
  exact (interval_card_le_finiteThetaSum hn hq hqp).trans_lt
    (finiteThetaSum_lt (by exact_mod_cast (show 2 ≤ q by omega))
      (indexLog_nonneg hq (by omega)))
end SharpIntermediateSubgroupBounds
