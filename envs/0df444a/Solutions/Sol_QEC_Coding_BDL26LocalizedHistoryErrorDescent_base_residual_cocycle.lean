-- Prove2me | solution 1 for QEC.Coding.BDL26LocalizedHistoryErrorDescent.base_residual_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:16:42.697769+00:00
-- url     : https://prove2.me/submissions/20210a05-503d-4bb2-a5f8-71c7d7b9fc89

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
import Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_path_syndrome

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
theorem _root_.solution :
    (Data S n).family.coboundary1 0
      ((path S n sigma tau top 0).word+(actualBase S n).decode (actualInputs S n sigma 0)+
        (actualBase S n).decode (actualInputs S n tau 0))=0 := by
  rw [map_add,map_add,path_syndrome,(actualBase S n).rightInverse,(actualBase S n).rightInverse]
  have hs := twice (actualInputs S n sigma 0).val
  have ht := twice (actualInputs S n tau 0).val
  change ((actualInputs S n sigma 0).val+(actualInputs S n tau 0).val)+
    (actualInputs S n sigma 0).val+(actualInputs S n tau 0).val=0
  calc
    _ = ((actualInputs S n sigma 0).val+(actualInputs S n sigma 0).val)+
        ((actualInputs S n tau 0).val+(actualInputs S n tau 0).val) := by abel
    _ = 0 := by rw [hs,ht,add_zero]
end QEC.Coding.BDL26LocalizedHistoryErrorDescent
