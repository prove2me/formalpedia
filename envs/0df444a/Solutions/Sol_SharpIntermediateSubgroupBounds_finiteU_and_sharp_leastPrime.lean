-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.finiteU_and_sharp_leastPrime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:06:07.023389+00:00
-- url     : https://prove2.me/submissions/6fd0d941-58e1-4682-908c-772198f95b54

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
import Theorems.Thm_SharpIntermediateSubgroupBounds_interval_card_lt_leastPrime_rpow
import Theorems.Thm_SharpIntermediateSubgroupBounds_finiteU_bound


set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
noncomputable section
universe u
variable {G : Type u} [Group G] [Fintype G]
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {H : Subgroup G} (hn : 1 < H.index) :
    ((Nat.card (interval H) : ℚ) ≤
        finiteUQ H.index H.index.minFac) ∧
      (Nat.card (interval H) : ℝ) <
        sharpConstant (H.index.minFac : ℝ) *
          (H.index : ℝ) ^
            (indexLog H.index.minFac H.index / 4) := by
  have hp : H.index.minFac.Prime := Nat.minFac_prime (by omega)
  exact ⟨finiteU_bound hn hp.one_lt le_rfl,
    interval_card_lt_leastPrime_rpow hn⟩
end SharpIntermediateSubgroupBounds
