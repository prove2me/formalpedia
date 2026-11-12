-- Prove2me | solution 1 for QEC.Coding.BDL26LocalizedHistoryErrorDescent.source_even_history
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:41:44.664909+00:00
-- url     : https://prove2.me/submissions/41298141-701e-4428-a70a-82fe6de11135

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
import Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_elementary_history

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
theorem _root_.solution (S : OddScale) (k : Nat) (hk : 1≤k)
    (sigma : TopInput S (2*(k-1))) (q : (state S (2*(k-1)+2)).presentation.Q) :
    2*(k-1)+2=2*k ∧
    (let n := 2*(k-1)
     let e := canonicalBasisWord (F := BDL26Field) q
     let x := elementaryCenter S n q
     let he := elementary_support S n q
     e+historyLiftedCorrection (Data S n) (actualHistory S n sigma)+
       historyLiftedCorrection (Data S n) (actualHistory S n (perturbTop S n sigma e))=
       intervalMap1 (Data S n) 0 (TopIndex n) (Nat.zero_le _)
         ((actualDescent S n sigma e x he 0).word+
           (actualBase S n).decode (actualInputs S n sigma 0)+
           (actualBase S n).decode (actualInputs S n (perturbTop S n sigma e) 0))+
       (Data S n).family.coboundary0 (TopIndex n) (actualPotential S n sigma e x he 0 (TopIndex n))) :=
  ⟨by omega,elementary_history S (2*(k-1)) sigma q⟩
end QEC.Coding.BDL26LocalizedHistoryErrorDescent
