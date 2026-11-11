-- Prove2me | solution 1 for QEC.Coding.BDL26HistorySyndromeSensitivity.actualInputs_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T06:30:28.424164+00:00
-- url     : https://prove2.me/submissions/2b969608-c029-40e5-8698-6657eff7e205

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Steps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_prefixInput_self

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open MultiscaleDecoder
open scoped Classical
universe u
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistorySyndromeSensitivity
theorem _root_.solution (sigma : TopInput S n) :
    actualInputs S n sigma (TopIndex n) = sigma :=
  prefixInput_self _ _ _ _ _
end QEC.Coding.BDL26HistorySyndromeSensitivity
