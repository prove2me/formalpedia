-- Prove2me | solution 1 for QEC.Coding.BDL26LocalizedHistoryErrorDescent.history_equation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:54:49.900377+00:00
-- url     : https://prove2.me/submissions/aa3441ff-728d-44b0-a59e-89cc234f70a9

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
import Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_path_top
import Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_interval_equation
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_assembledPrefix_split
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_assembledPrefix_top
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_assembledPrefix_zero
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_word_toggle


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalizedHistoryErrorDescent
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
variable (top : LocalizedWord S n sigma tau (TopIndex n))
namespace QEC.Coding.BDL26LocalizedHistoryErrorDescent
theorem _root_.solution :
    top.word+historyLiftedCorrection (Data S n) (actualHistory S n sigma)+
        historyLiftedCorrection (Data S n) (actualHistory S n tau)=
      intervalMap1 (Data S n) 0 (TopIndex n) (Nat.zero_le _)
        ((path S n sigma tau top 0).word+(actualBase S n).decode (actualInputs S n sigma 0)+
          (actualBase S n).decode (actualInputs S n tau 0))+
      (Data S n).family.coboundary0 (TopIndex n)
        (intervalPotential S n sigma tau top 0 (TopIndex n)) := by
  have hi := interval_equation S n sigma tau top 0 (TopIndex n) (Nat.zero_le _)
  rw [path_top] at hi
  have hs := assembledPrefix_split S n sigma 0 (TopIndex n) (Nat.zero_le _)
  have ht := assembledPrefix_split S n tau 0 (TopIndex n) (Nat.zero_le _)
  rw [assembledPrefix_top,assembledPrefix_zero] at hs ht
  have hm : top.word+correctionIntervalSum S n sigma 0 (TopIndex n)+
      correctionIntervalSum S n tau 0 (TopIndex n)=
      intervalMap1 (Data S n) 0 (TopIndex n) (Nat.zero_le _) (path S n sigma tau top 0).word+
        (Data S n).family.coboundary0 (TopIndex n)
          (intervalPotential S n sigma tau top 0 (TopIndex n)) :=
    BDL26HistoryErrorTelescoping.word_toggle _ _ _ hi
  rw [hs,ht,map_add,map_add]
  calc
    _ = (top.word+correctionIntervalSum S n sigma 0 (TopIndex n)+
        correctionIntervalSum S n tau 0 (TopIndex n))+
      intervalMap1 (Data S n) 0 (TopIndex n) (Nat.zero_le _)
        ((actualBase S n).decode (actualInputs S n sigma 0))+
      intervalMap1 (Data S n) 0 (TopIndex n) (Nat.zero_le _)
        ((actualBase S n).decode (actualInputs S n tau 0)) := by ac_rfl
    _ = _ := by rw [hm]; ac_rfl
end QEC.Coding.BDL26LocalizedHistoryErrorDescent
