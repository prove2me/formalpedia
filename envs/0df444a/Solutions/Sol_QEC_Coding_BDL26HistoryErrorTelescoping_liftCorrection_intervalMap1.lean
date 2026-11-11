-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.liftCorrection_intervalMap1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:29:43.91742+00:00
-- url     : https://prove2.me/submissions/c70eeafb-39b7-4c20-a69e-096e7a8daa4f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_Intervals
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_intervalMap1_self
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_intervalMap1_succ
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_liftCorrection_map1_eq


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
    (b : Nat) (hb : b ≤ depth) (a : LevelIndex depth) (ha : a.val ≤ b)
    (w : D.family.Cochain1 a) :
    liftCorrection D ⟨b,Nat.lt_succ_of_le hb⟩
      (intervalMap1 D a ⟨b,Nat.lt_succ_of_le hb⟩ ha w) = liftCorrection D a w := by
  induction b generalizing a with
  | zero =>
      have he : a = ⟨0,Nat.lt_succ_of_le hb⟩ := Fin.ext (by change a.val = 0; omega)
      subst a
      rw [intervalMap1_self]
      rfl
  | succ b ih =>
      by_cases he : a.val = b+1
      · have he' : a = ⟨b+1,Nat.lt_succ_of_le hb⟩ := Fin.ext he
        subst a
        rw [intervalMap1_self]
        rfl
      · have hal : a.val ≤ b := by omega
        let i : StepIndex depth := ⟨b,Nat.lt_of_lt_of_le (Nat.lt_succ_self b) hb⟩
        change liftCorrection D i.succ (intervalMap1 D a i.succ ha w) = liftCorrection D a w
        rw [intervalMap1_succ D a i hal]
        change liftCorrection D i.succ
          ((D.selectedMap i).map1 (intervalMap1 D a i.castSucc hal w)) = _
        rw [← liftCorrection_map1_eq]
        exact ih (by omega) a hal w
end QEC.Coding.BDL26HistoryErrorTelescoping
