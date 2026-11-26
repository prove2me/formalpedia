-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.elementary_interval_bound_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:04:50.848796+00:00
-- url     : https://prove2.me/submissions/6e711c3d-3f5d-454e-aae7-9f4dd1e694b4

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
import Theorems.Thm_SharpIntermediateSubgroupBounds_elementary_interval_bound


set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
noncomputable section
universe u
variable {G : Type u} [Group G] [Fintype G]
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {H : Subgroup G} (hn : 1 < H.index) :
    (Nat.card (interval H) : ℝ) ≤
      (H.index : ℝ) ^ indexLog 2 H.index := by
  have hnat := elementary_interval_bound hn
  have hcast :
      (Nat.card (interval H) : ℝ) ≤
        (H.index : ℝ) ^ Nat.log 2 H.index := by
    exact_mod_cast hnat
  calc
    (Nat.card (interval H) : ℝ) ≤
        (H.index : ℝ) ^ Nat.log 2 H.index := hcast
    _ = (H.index : ℝ) ^ (Nat.log 2 H.index : ℝ) := by
      rw [Real.rpow_natCast]
    _ ≤ (H.index : ℝ) ^ indexLog 2 H.index := by
      apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ H.index by omega))
      rw [indexLog, Real.log_div_log]
      exact Real.natLog_le_logb H.index 2
end SharpIntermediateSubgroupBounds
