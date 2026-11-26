-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.sharpScale_eq_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:50:21.22943+00:00
-- url     : https://prove2.me/submissions/310277d1-e0bb-4802-9193-d4aab2798c05

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
    sharpScale q n = (n : ℝ) ^ (indexLog q n / 4) := by
  rw [sharpScale, Real.rpow_def_of_pos (by exact_mod_cast hn)]
  unfold indexLog
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hlogq : Real.log (q : ℝ) ≠ 0 := (Real.log_pos hqR).ne'
  congr 1
  field_simp
end SharpIntermediateSubgroupBounds
