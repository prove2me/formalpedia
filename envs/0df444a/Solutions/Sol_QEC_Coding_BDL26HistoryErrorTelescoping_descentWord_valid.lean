-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.descentWord_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:50:45.121963+00:00
-- url     : https://prove2.me/submissions/ab47f3e6-e103-4e66-b292-8154af78cbdc

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_actualInputs_prefix
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_actualInputs_readout
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_errorDown_valid
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open scoped Classical
universe u v w
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistoryErrorTelescoping
theorem _root_.solution (sigma : TopInput S n) (b : LevelIndex n)
    (u : (SuffixData S n).family.Cochain1 b)
    (hu : (SuffixData S n).family.coboundary1 b u = actualReadout S n sigma b)
    (a : LevelIndex n) (ha : a.val ≤ b.val) :
    (SuffixData S n).family.coboundary1 a (descentWord S n b u a ha) =
      (actualInputs S n sigma a).val := by
  have hin := hu.trans (actualInputs_readout S n sigma b)
  have hd := errorDown_valid S n b.val (Nat.le_of_lt_succ b.isLt) u
    (actualInputs S n sigma b) hin a ha
  exact hd.trans (congrArg Subtype.val (actualInputs_prefix S n sigma a b ha))
end QEC.Coding.BDL26HistoryErrorTelescoping
