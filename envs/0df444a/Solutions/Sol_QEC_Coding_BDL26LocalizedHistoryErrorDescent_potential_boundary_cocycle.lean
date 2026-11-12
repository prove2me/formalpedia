-- Prove2me | solution 1 for QEC.Coding.BDL26LocalizedHistoryErrorDescent.potential_boundary_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:37:14.267329+00:00
-- url     : https://prove2.me/submissions/0efcc1d4-3f38-45bc-8e45-8e0e3a60b41f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_BDL26CochainFamily_coboundary1_comp_coboundary0


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
theorem _root_.solution (a b : LevelIndex n) :
    (Data S n).family.coboundary1 b
      ((Data S n).family.coboundary0 b (intervalPotential S n sigma tau top a b))=0 :=
  LinearMap.congr_fun ((Data S n).family.coboundary1_comp_coboundary0 b) _
end QEC.Coding.BDL26LocalizedHistoryErrorDescent
