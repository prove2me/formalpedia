-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.intervalMap0_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:28:49.631926+00:00
-- url     : https://prove2.me/submissions/4d9a2fcb-18db-419e-b703-b20ac9d957b3

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_Intervals
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_linearUp_comp
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


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
    (a b c : LevelIndex depth) (hab : a.val ≤ b.val) (hbc : b.val ≤ c.val) :
    intervalMap0 D a c (hab.trans hbc) =
      (intervalMap0 D b c hbc).comp (intervalMap0 D a b hab) :=
  linearUp_comp _ c.val _ b a hbc hab
end QEC.Coding.BDL26HistoryErrorTelescoping
