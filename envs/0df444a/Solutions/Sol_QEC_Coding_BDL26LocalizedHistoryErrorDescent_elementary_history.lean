-- Prove2me | solution 1 for QEC.Coding.BDL26LocalizedHistoryErrorDescent.elementary_history
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T19:32:06.245612+00:00
-- url     : https://prove2.me/submissions/108c585a-5994-4205-a416-fd2f5b98984d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
import Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_actual_history

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
theorem _root_.solution (S : OddScale) (n : Nat) (sigma : TopInput S n)
    (q : (state S (n+2)).presentation.Q) :
    let e := canonicalBasisWord (F := BDL26Field) q
    let x := elementaryCenter S n q
    let he := elementary_support S n q
    e+historyLiftedCorrection (Data S n) (actualHistory S n sigma)+
      historyLiftedCorrection (Data S n) (actualHistory S n (perturbTop S n sigma e))=
      intervalMap1 (Data S n) 0 (TopIndex n) (Nat.zero_le _)
        ((actualDescent S n sigma e x he 0).word+
          (actualBase S n).decode (actualInputs S n sigma 0)+
          (actualBase S n).decode (actualInputs S n (perturbTop S n sigma e) 0))+
      (Data S n).family.coboundary0 (TopIndex n) (actualPotential S n sigma e x he 0 (TopIndex n)) :=
  actual_history S n sigma (canonicalBasisWord (F := BDL26Field) q) (elementaryCenter S n q) (elementary_support S n q)
end QEC.Coding.BDL26LocalizedHistoryErrorDescent
