-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.actualCorrection_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:28:52.000195+00:00
-- url     : https://prove2.me/submissions/dd219e5d-9fad-42f0-afee-6326242bb6bc

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_assembledPrefix_split
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_assembledPrefix_top
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_assembledPrefix_zero

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
    historyLiftedCorrection (SuffixData S n) (actualHistory S n sigma) =
      correctionIntervalSum S n sigma 0 (TopIndex n) +
        intervalMap1 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _)
          ((actualBase S n).decode (actualInputs S n sigma 0)) := by
  rw [← assembledPrefix_top,assembledPrefix_split S n sigma 0 (TopIndex n) (Nat.zero_le _),
    assembledPrefix_zero]
end QEC.Coding.BDL26HistoryErrorTelescoping
