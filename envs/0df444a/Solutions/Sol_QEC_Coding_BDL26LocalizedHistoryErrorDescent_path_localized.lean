-- Prove2me | solution 1 for QEC.Coding.BDL26LocalizedHistoryErrorDescent.path_localized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:08:18.461358+00:00
-- url     : https://prove2.me/submissions/91d1cd0c-a3df-43c1-9263-2b302e2512f0

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalizedHistoryErrorDescent
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
variable (top : LocalizedWord S n sigma tau (TopIndex n))
namespace QEC.Coding.BDL26LocalizedHistoryErrorDescent
theorem _root_.solution (a : LevelIndex n) :
    hammingSupport (path S n sigma tau top a).word ⊆
      star S n a (path S n sigma tau top a).center :=
  (path S n sigma tau top a).supported
end QEC.Coding.BDL26LocalizedHistoryErrorDescent
