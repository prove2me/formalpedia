-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.snapshotWords_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:10:09.243661+00:00
-- url     : https://prove2.me/submissions/427fb6ae-0ca2-46c3-ad00-426d0289ed7c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_correctionIntervalSum_self
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_correctionIntervalSum_succ
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_snapshotWords_zero_eq
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_snapshotWords_succ_eq
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_linearMap_list_sum
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_sum


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26DecodingGraph
open scoped Classical
universe u v
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistoryErrorTelescoping
theorem _root_.solution (sigma : TopInput S n) (a : LevelIndex n)
    (b : Nat) (hb : b ≤ n) (ha : a.val ≤ b) :
    (snapshotWords S n sigma a b hb ha).sum =
      correctionIntervalSum S n sigma a ⟨b,Nat.lt_succ_of_le hb⟩ := by
  induction b with
  | zero =>
      have he : a = ⟨0,Nat.lt_succ_of_le hb⟩ := Fin.ext (by change a.val = 0; omega)
      subst a
      rw [correctionIntervalSum_self,snapshotWords_zero_eq] <;> rfl
  | succ b ih =>
      by_cases he : a.val = b+1
      · have he' : a = ⟨b+1,Nat.lt_succ_of_le hb⟩ := Fin.ext he
        subst a
        rw [correctionIntervalSum_self,snapshotWords_succ_eq,dif_pos he,List.sum_nil]
      · have hal : a.val ≤ b := by omega
        let i : StepIndex n := ⟨b,Nat.lt_of_lt_of_le (Nat.lt_succ_self b) hb⟩
        rw [snapshotWords_succ_eq,dif_neg he]
        change ((actualOutput S n sigma i).correction ::
          (snapshotWords S n sigma a b (by omega) hal).map ((SuffixData S n).selectedMap i).map1).sum =
          correctionIntervalSum S n sigma a i.succ
        have ht := ih (by omega) hal
        change (snapshotWords S n sigma a b (by omega) hal).sum =
          correctionIntervalSum S n sigma a i.castSucc at ht
        rw [List.sum_cons,linearMap_list_sum,ht,
          correctionIntervalSum_succ S n sigma a i hal]
        exact add_comm _ _
end QEC.Coding.BDL26HistoryErrorTelescoping
