-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.intervalMap1_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:33:53.31523+00:00
-- url     : https://prove2.me/submissions/7a99c9c3-c952-493c-8d36-afd8988964fb

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_Intervals
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_liftCorrection_intervalMap1
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_liftCorrection_top


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
    (a : LevelIndex depth) (w : D.family.Cochain1 a) :
    intervalMap1 D a (TopIndex depth) (Nat.le_of_lt_succ a.isLt) w =
      liftCorrection D a w := by
  have h := liftCorrection_intervalMap1 D depth (Nat.le_refl _) a
    (Nat.le_of_lt_succ a.isLt) w
  rw [liftCorrection_top] at h
  exact h
end QEC.Coding.BDL26HistoryErrorTelescoping
