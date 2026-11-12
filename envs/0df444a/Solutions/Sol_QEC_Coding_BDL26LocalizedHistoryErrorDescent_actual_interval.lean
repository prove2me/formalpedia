-- Prove2me | solution 1 for QEC.Coding.BDL26LocalizedHistoryErrorDescent.actual_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:40:36.937854+00:00
-- url     : https://prove2.me/submissions/ad012e0d-44c4-4216-9eec-e878174ba3af

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
import Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_interval_equation

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalizedHistoryErrorDescent
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
variable (top : LocalizedWord S n sigma tau (TopIndex n))
variable (e : (Data S n).family.Cochain1 (TopIndex n))
variable (x : (state S (n+2)).presentation.X) (he : hammingSupport e ⊆ star S n (TopIndex n) x)
namespace QEC.Coding.BDL26LocalizedHistoryErrorDescent
theorem _root_.solution (a b : LevelIndex n) (hab : a.val≤b.val) :
    intervalMap1 (Data S n) a b hab (actualDescent S n sigma e x he a).word=
      (actualDescent S n sigma e x he b).word+correctionIntervalSum S n sigma a b+
        correctionIntervalSum S n (perturbTop S n sigma e) a b+
        (Data S n).family.coboundary0 b (actualPotential S n sigma e x he a b) :=
  interval_equation S n sigma (perturbTop S n sigma e) (initial S n sigma e x he) a b hab
end QEC.Coding.BDL26LocalizedHistoryErrorDescent
