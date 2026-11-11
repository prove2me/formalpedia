-- Prove2me | solution 1 for QEC.Coding.BDL26LocalizedHistoryErrorDescent.depth_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:30:01.491914+00:00
-- url     : https://prove2.me/submissions/ef2031e9-49e3-4858-a944-184002bd1e8c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
import Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_actualDescent_top
import Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_actual_empty_interval

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
theorem _root_.solution (S : OddScale) (sigma : TopInput S 0)
    (e : (Data S 0).family.Cochain1 (TopIndex 0))
    (x : (state S 2).presentation.X) (he : hammingSupport e⊆star S 0 (TopIndex 0) x) :
    (actualDescent S 0 sigma e x he 0).word=e ∧ actualPotential S 0 sigma e x he 0 0=0 := by
  constructor
  · exact actualDescent_top S 0 sigma e x he
  · exact (actual_empty_interval S 0 sigma e x he 0).1
end QEC.Coding.BDL26LocalizedHistoryErrorDescent
