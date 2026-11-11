-- Prove2me | solution 1 for QEC.Coding.BDL26HistorySyndromeSensitivity.actualReadout_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:58:56.466054+00:00
-- url     : https://prove2.me/submissions/0f1124aa-2c29-4619-ac0f-80ad5431e781

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Preimages
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_actualInputs_readout
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_actualInputs_top


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26RXCoarseInfluence BDL26RXInfluenceBounds MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (d : Nat) (i : StepIndex d)
variable (n : Nat)
namespace QEC.Coding.BDL26HistorySyndromeSensitivity
theorem _root_.solution (sigma : TopInput S n) :
    actualReadout S n sigma (TopIndex n) = sigma.val := by
  rw [actualInputs_readout, actualInputs_top]
end QEC.Coding.BDL26HistorySyndromeSensitivity
