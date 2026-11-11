-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.intervalMap1_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T06:54:24.083978+00:00
-- url     : https://prove2.me/submissions/987a87c5-b749-4d34-98a4-7b62c23aff66

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_Intervals
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_linearUp_succ

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
    (a : LevelIndex depth) (i : StepIndex depth) (hai : a.val ≤ i.val) :
    intervalMap1 D a i.succ (by change a.val ≤ i.val+1; omega) =
      ((D.selectedMap i).map1).comp (intervalMap1 D a i.castSucc hai) :=
  linearUp_succ _ i.val (Nat.le_of_lt_succ i.succ.isLt) a hai
end QEC.Coding.BDL26HistoryErrorTelescoping
