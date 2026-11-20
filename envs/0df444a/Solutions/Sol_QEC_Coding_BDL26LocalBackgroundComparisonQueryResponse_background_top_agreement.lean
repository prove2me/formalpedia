-- Prove2me | solution 1 for QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse.background_top_agreement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T14:47:04.299613+00:00
-- url     : https://prove2.me/submissions/f668342b-ff1e-4f81-850c-a4a1bb888d40

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonDepth
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonQueryResponse
import Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonQueryResponse_pullback_agreement
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffix_delta1


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26RZMap1CoordinateBridge
open BDL26HistoryLogicalResidual (suffix_delta1)
open BDL26LocalBackgroundComparisonResponse BDL26PairedHistoryQueryCone
open MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse
theorem _root_.solution (sigma0 : TopInput S n) (g : W S n)
    (A : Finset (Coordinates S n (TopIndex n))) :
    AgreeOn A (perturbTop S n sigma0 g).val
      (perturbTop S n sigma0 (backgroundRestriction S n g (physicalPullback S n A))).val := by
  intro z hz
  exact congrArg (fun t => sigma0.val z+t) (pullback_agreement S n g A z hz)
end QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse
