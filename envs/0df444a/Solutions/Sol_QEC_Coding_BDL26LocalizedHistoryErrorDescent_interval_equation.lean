-- Prove2me | solution 1 for QEC.Coding.BDL26LocalizedHistoryErrorDescent.interval_equation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:46:11.854594+00:00
-- url     : https://prove2.me/submissions/3680293a-1def-4681-adbd-423cff81e10f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
import Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_interval_equation_nat

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
theorem _root_.solution (a b : LevelIndex n) (hab : a.val≤b.val) :
    intervalMap1 (Data S n) a b hab (path S n sigma tau top a).word=
      (path S n sigma tau top b).word+correctionIntervalSum S n sigma a b+
        correctionIntervalSum S n tau a b+(Data S n).family.coboundary0 b
          (intervalPotential S n sigma tau top a b) :=
  interval_equation_nat S n sigma tau top b.val (Nat.le_of_lt_succ b.isLt) a hab
end QEC.Coding.BDL26LocalizedHistoryErrorDescent
