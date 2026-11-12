-- Prove2me | solution 1 for QEC.Coding.BDL26LocalizedHistoryErrorDescent.actual_potential_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:40:48.707196+00:00
-- url     : https://prove2.me/submissions/22e153da-253d-4782-8d5d-d05235659187

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
import Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_intervalPotential_comp

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
theorem _root_.solution (a b c : LevelIndex n) (hab : a.val≤b.val) (hbc : b.val≤c.val) :
    actualPotential S n sigma e x he a c=actualPotential S n sigma e x he b c+
      intervalMap0 (Data S n) b c hbc (actualPotential S n sigma e x he a b) :=
  intervalPotential_comp S n sigma (perturbTop S n sigma e) (initial S n sigma e x he) a b c hab hbc
end QEC.Coding.BDL26LocalizedHistoryErrorDescent
