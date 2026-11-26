-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.natFloor_indexLog
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:44:40.926865+00:00
-- url     : https://prove2.me/submissions/68dcc5bf-ad88-43c3-bdc0-71e1bf19d2f5

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
theorem _root_.solution (q n : ℕ) :
    Nat.floor (indexLog q n) = Nat.log q n := by
  rw [indexLog, Real.log_div_log, Real.natFloor_logb_natCast]
end SharpIntermediateSubgroupBounds
