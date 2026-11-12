-- Prove2me | solution 1 for QEC.Coding.BDL26HistorySyndromeSensitivity.depthTwo_readout
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:08:01.591082+00:00
-- url     : https://prove2.me/submissions/0a962d16-b2aa-418d-9271-9f9ff34ea767

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Preimages
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_actualReadout_top

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26RXCoarseInfluence BDL26RXInfluenceBounds MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (d : Nat) (i : StepIndex d)
variable (n : Nat)
namespace QEC.Coding.BDL26HistorySyndromeSensitivity
theorem _root_.solution (sigma : TopInput S 0) : actualReadout S 0 sigma 0 = sigma.val :=
  actualReadout_top S 0 sigma
end QEC.Coding.BDL26HistorySyndromeSensitivity
