-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.actual_fullspan
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:38:56.148008+00:00
-- url     : https://prove2.me/submissions/45eeff72-d66c-4414-b935-cd59e4a987fc

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_word_toggle
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_descentWord_self
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_actual_assembled_interval
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_assembledPrefix_top
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_assembledPrefix_zero
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_actualReadout_top
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open scoped Classical
universe u v w
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistoryErrorTelescoping
theorem _root_.solution (sigma : TopInput S n)
    (u : (SuffixData S n).family.Cochain1 (TopIndex n))
    (hu : (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val) :
    intervalMap1 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _)
        (descentWord S n (TopIndex n) u 0 (Nat.zero_le _) +
          (actualBase S n).decode (actualInputs S n sigma 0)) =
      u + historyLiftedCorrection (SuffixData S n) (actualHistory S n sigma) +
        (SuffixData S n).family.coboundary0 (TopIndex n)
          (accumulatedPotential S n (TopIndex n) u 0 n (Nat.le_refl _) (Nat.zero_le _)) := by
  have hv : (SuffixData S n).family.coboundary1 (TopIndex n) u =
      actualReadout S n sigma (TopIndex n) := hu.trans (actualReadout_top S n sigma).symm
  have h := actual_assembled_interval S n sigma (TopIndex n) u hv 0 (TopIndex n)
    (Nat.zero_le _) (Nat.le_refl _)
  rw [descentWord_self,assembledPrefix_top,assembledPrefix_zero] at h
  exact word_toggle _ _ _ h
end QEC.Coding.BDL26HistoryErrorTelescoping
