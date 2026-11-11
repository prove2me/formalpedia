-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.assembledPrefix_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:46:28.522318+00:00
-- url     : https://prove2.me/submissions/4381f01e-b626-4de6-9852-bd4ac4556ed3

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_historyPrefixSum_top

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
theorem _root_.solution (sigma : TopInput S n) :
    assembledPrefix S n sigma (TopIndex n) =
      historyLiftedCorrection (SuffixData S n) (actualHistory S n sigma) :=
  historyPrefixSum_top _ _
end QEC.Coding.BDL26HistoryErrorTelescoping
