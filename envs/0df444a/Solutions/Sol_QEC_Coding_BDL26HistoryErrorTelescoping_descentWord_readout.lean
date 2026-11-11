-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.descentWord_readout
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T13:28:59.576355+00:00
-- url     : https://prove2.me/submissions/354c4cc0-6126-4a82-97f4-9f2a4b61fd76

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_descentWord_valid
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_actualInputs_readout
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
theorem _root_.solution (sigma : TopInput S n) (b : LevelIndex n)
    (u : (SuffixData S n).family.Cochain1 b)
    (hu : (SuffixData S n).family.coboundary1 b u = actualReadout S n sigma b)
    (a : LevelIndex n) (ha : a.val ≤ b.val) :
    (SuffixData S n).family.coboundary1 a (descentWord S n b u a ha) =
      actualReadout S n sigma a :=
  (descentWord_valid S n sigma b u hu a ha).trans (actualInputs_readout S n sigma a).symm
end QEC.Coding.BDL26HistoryErrorTelescoping
