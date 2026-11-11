-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.intervalMap1_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T06:53:16.490348+00:00
-- url     : https://prove2.me/submissions/0df3d2da-a355-42bd-abca-4f1169820f0a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_Intervals
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_linearUp_self

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder
open scoped Classical
universe u v
variable {depth : Nat} {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
namespace QEC.Coding.BDL26HistoryErrorTelescoping
theorem _root_.solution (D : BDL26DecoderData depth C0 C1 C2)
    (a : LevelIndex depth) : intervalMap1 D a a (Nat.le_refl _) = LinearMap.id :=
  linearUp_self _ a.val _
end QEC.Coding.BDL26HistoryErrorTelescoping
