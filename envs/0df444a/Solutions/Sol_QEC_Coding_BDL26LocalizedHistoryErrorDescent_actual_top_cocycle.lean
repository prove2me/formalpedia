-- Prove2me | solution 1 for QEC.Coding.BDL26LocalizedHistoryErrorDescent.actual_top_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:41:19.792294+00:00
-- url     : https://prove2.me/submissions/880e37fb-fb5e-4e4c-b96b-0afd7df87ea4

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
import Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_actualHistory_syndrome


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
    (Data S n).family.coboundary1 (TopIndex n)
      (e+historyLiftedCorrection (Data S n) (actualHistory S n sigma)+
        historyLiftedCorrection (Data S n) (actualHistory S n (perturbTop S n sigma e)))=0 := by
  rw [map_add,map_add]
  have hs : (Data S n).family.coboundary1 (TopIndex n)
      (historyLiftedCorrection (Data S n) (actualHistory S n sigma))=sigma.val :=
    actualHistory_syndrome S n sigma
  have ht : (Data S n).family.coboundary1 (TopIndex n)
      (historyLiftedCorrection (Data S n) (actualHistory S n (perturbTop S n sigma e)))=
        (perturbTop S n sigma e).val := actualHistory_syndrome S n (perturbTop S n sigma e)
  rw [hs,ht]
  change (Data S n).family.coboundary1 (TopIndex n) e+sigma.val+
    (sigma.val+(Data S n).family.coboundary1 (TopIndex n) e)=0
  calc
    _ = ((Data S n).family.coboundary1 (TopIndex n) e+
        (Data S n).family.coboundary1 (TopIndex n) e)+(sigma.val+sigma.val) := by ac_rfl
    _ = 0 := by rw [twice,twice,add_zero]
end QEC.Coding.BDL26LocalizedHistoryErrorDescent
