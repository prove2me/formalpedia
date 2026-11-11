-- Prove2me | solution 1 for QEC.Coding.BDL26LocalizedHistoryErrorDescent.path_syndrome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:08:15.256067+00:00
-- url     : https://prove2.me/submissions/3fde4979-12a4-4039-be2c-f29849feec92

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
    (Data S n).family.coboundary1 a (path S n sigma tau top a).word=
      (actualInputs S n sigma a).val+(actualInputs S n tau a).val :=
  (path S n sigma tau top a).syndrome
end QEC.Coding.BDL26LocalizedHistoryErrorDescent
