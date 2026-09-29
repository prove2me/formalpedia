-- Prove2me | solution 1 for R03FixedPerfectMatchingBridge.perfectMatching_isMatchingRelation
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T01:34:55.828972+00:00
-- url     : https://prove2.me/submissions/a6277b82-1579-4129-a690-067feea4fb78

import Mathlib
import Definitions.Def_cubic_p3_partition_models
import Definitions.Def_r03_defs_e1150db1c7_w64_fixed_perfect_matching_bridge_v1

namespace R03FixedPerfectMatchingBridge

open CubicP3Partition

universe u

variable {V : Type u} [Fintype V]

end R03FixedPerfectMatchingBridge

open R03FixedPerfectMatchingBridge
open CubicP3Partition
universe u
variable {V : Type u} [Fintype V]
theorem solution
    {G M : SimpleGraph V} (hM : PerfectMatching G M) :
    IsMatchingRelation M := by
  classical
  intro v a b hav hbv
  have hcard : Fintype.card {w : V // M.Adj v w} = 1 := by
    simpa [CubicP3Partition.degree, Nat.card_eq_fintype_card] using hM.2 v
  obtain ⟨w, hw⟩ := (Fintype.card_eq_one_iff.mp hcard)
  have ha : (⟨a, hav⟩ : {w : V // M.Adj v w}) = w := hw _
  have hb : (⟨b, hbv⟩ : {w : V // M.Adj v w}) = w := hw _
  exact congrArg Subtype.val (ha.trans hb.symm)
