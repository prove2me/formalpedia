-- Prove2me | solution 1 for QEC.Coding.BDL26LocalizedHistoryErrorDescent.actual_history
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T19:11:58.964473+00:00
-- url     : https://prove2.me/submissions/10618d3a-55f6-4576-8e89-0d06d8011ca1

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
import Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_history_equation

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
theorem _root_.solution :
    e+historyLiftedCorrection (Data S n) (actualHistory S n sigma)+
      historyLiftedCorrection (Data S n) (actualHistory S n (perturbTop S n sigma e))=
      intervalMap1 (Data S n) 0 (TopIndex n) (Nat.zero_le _)
        ((actualDescent S n sigma e x he 0).word+
          (actualBase S n).decode (actualInputs S n sigma 0)+
          (actualBase S n).decode (actualInputs S n (perturbTop S n sigma e) 0))+
      (Data S n).family.coboundary0 (TopIndex n) (actualPotential S n sigma e x he 0 (TopIndex n)) :=
  history_equation S n sigma (perturbTop S n sigma e) (initial S n sigma e x he)
end QEC.Coding.BDL26LocalizedHistoryErrorDescent
