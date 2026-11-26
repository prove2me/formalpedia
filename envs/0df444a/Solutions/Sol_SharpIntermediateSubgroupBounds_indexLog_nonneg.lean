-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.indexLog_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:00:34.513441+00:00
-- url     : https://prove2.me/submissions/27c576ed-fe49-4562-bee9-2837783e128d

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

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
noncomputable section
universe u
variable {G : Type u} [Group G] [Fintype G]
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {q n : ℕ} (hq : 1 < q) (hn : 0 < n) :
    0 ≤ indexLog q n := by
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn.ne')
  exact div_nonneg (Real.log_nonneg hnR) (Real.log_pos hqR).le
end SharpIntermediateSubgroupBounds
