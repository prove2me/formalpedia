-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.interval_card_le_finiteThetaSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:02:38.507284+00:00
-- url     : https://prove2.me/submissions/323ba594-c426-4075-84f9-c4535c77f2d6

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
import Theorems.Thm_SharpIntermediateSubgroupBounds_ratCast_finiteUQ_eq_finiteThetaSum
import Theorems.Thm_SharpIntermediateSubgroupBounds_finiteU_bound


set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
noncomputable section
universe u
variable {G : Type u} [Group G] [Fintype G]
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {H : Subgroup G} (hn : 1 < H.index)
    {q : ℕ} (hq : 1 < q) (hqp : q ≤ H.index.minFac) :
    (Nat.card (interval H) : ℝ) ≤
      finiteThetaSum (q : ℝ) (indexLog q H.index) := by
  have hQ := finiteU_bound hn hq hqp
  have hR :
      (((Nat.card (interval H) : ℚ) : ℝ)) ≤
        ((finiteUQ H.index q : ℚ) : ℝ) := by
    exact_mod_cast hQ
  rw [ratCast_finiteUQ_eq_finiteThetaSum hq (by omega)] at hR
  exact_mod_cast hR
end SharpIntermediateSubgroupBounds
