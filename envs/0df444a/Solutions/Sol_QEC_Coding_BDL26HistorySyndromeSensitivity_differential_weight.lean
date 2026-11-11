-- Prove2me | solution 1 for QEC.Coding.BDL26HistorySyndromeSensitivity.differential_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:33:11.235567+00:00
-- url     : https://prove2.me/submissions/26990eaa-27b3-42cc-89ce-94df744bd3fa

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Preimages
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_differential_support
import Theorems.Thm_QEC_Coding_BDL26RXInfluenceBounds_basisSyndrome_weight_le_four
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26RXCoarseInfluence BDL26RXInfluenceBounds MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (d : Nat) (i : StepIndex d)
namespace QEC.Coding.BDL26HistorySyndromeSensitivity
theorem _root_.solution (e : (indexedFamily S d).Cochain1 i.succ) :
    HammingWeight ((indexedFamily S d).coboundary1 i.succ e) ≤ 4 * HammingWeight e := by
  have hs := Finset.card_le_card (differential_support S d i e)
  have hc := Finset.card_biUnion_le_card_mul (hammingSupport e)
    (fun q => hammingSupport (basisSyndrome S d i q)) 4
    (fun q _ => basisSyndrome_weight_le_four S d i q)
  exact hs.trans (hc.trans_eq (Nat.mul_comm _ _))
end QEC.Coding.BDL26HistorySyndromeSensitivity
