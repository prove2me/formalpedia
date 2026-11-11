-- Prove2me | solution 1 for QEC.Coding.BDL26UniformHistoryObstruction.uniform_rx_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:39:28.014377+00:00
-- url     : https://prove2.me/submissions/72ded31f-26d1-4c62-a2e8-01708eb5e7d0

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26OwnerParentObstruction MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26UniformHistoryObstruction
theorem _root_.solution (j : Nat) : ((2 * j + 2) + 1) / 2 = j + 1 := by omega
end QEC.Coding.BDL26UniformHistoryObstruction
