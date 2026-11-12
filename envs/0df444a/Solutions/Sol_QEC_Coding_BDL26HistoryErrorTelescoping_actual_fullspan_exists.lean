-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.actual_fullspan_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:35:02.863426+00:00
-- url     : https://prove2.me/submissions/8e90fc37-8a92-45a5-907c-1b57c5f04961

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_descentWord_readout
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_actual_fullspan
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
theorem _root_.solution (sigma : TopInput S n) :
    ∃ (l : (SuffixData S n).family.Cochain1 0)
      (q : (SuffixData S n).family.Cochain0 (TopIndex n)),
      (SuffixData S n).family.coboundary1 0 l = actualReadout S n sigma 0 ∧
      ∃ u : (SuffixData S n).family.Cochain1 (TopIndex n),
        (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val ∧
        intervalMap1 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _)
          (l + (actualBase S n).decode (actualInputs S n sigma 0)) =
          u + historyLiftedCorrection (SuffixData S n) (actualHistory S n sigma) +
            (SuffixData S n).family.coboundary0 (TopIndex n) q := by
  obtain ⟨u,hu⟩ := sigma.property
  have hv := hu.trans (actualReadout_top S n sigma).symm
  exact ⟨descentWord S n (TopIndex n) u 0 (Nat.zero_le _),
    accumulatedPotential S n (TopIndex n) u 0 n (Nat.le_refl _) (Nat.zero_le _),
    descentWord_readout S n sigma (TopIndex n) u hv 0 (Nat.zero_le _),u,hu,
    actual_fullspan S n sigma u hu⟩
end QEC.Coding.BDL26HistoryErrorTelescoping
