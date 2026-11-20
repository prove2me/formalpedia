-- Prove2me | solution 1 for QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse.residual_restriction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T15:00:47.341518+00:00
-- url     : https://prove2.me/submissions/ab6582bc-d8de-4cb7-be6a-fd8eb0795f37

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonDepth
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonQueryResponse
import Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonQueryResponse_background_top_agreement
import Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonQueryResponse_full_pair_replay
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffix_delta1
import Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_stoppingLevel_coalesces


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
theorem _root_.solution (sigma0 : TopInput S n) (g e : W S n) :
    BDL26AllDepthBottomComparisonStability.residual S n (perturbTop S n sigma0 g) e =
      BDL26AllDepthBottomComparisonStability.residual S n
        (perturbTop S n sigma0 (backgroundRestriction S n g (queryMask S n sigma0 g e))) e := by
  let s := perturbTop S n sigma0 g
  let a := queryStop S n sigma0 g e
  let t := perturbTop S n sigma0 (backgroundRestriction S n g (queryMask S n sigma0 g e))
  have hstop : a.val = 0 ∨ actualInputs S n s a = actualInputs S n (perturbTop S n s e) a := by
    by_cases hz : a.val = 0
    · exact Or.inl hz
    · exact Or.inr (stoppingLevel_coalesces S n s e (by change 0 < a.val; omega))
  have ha : AgreeOn (queries S n e a (TopIndex n)) s.val t.val :=
    background_top_agreement S n sigma0 g (topQueries S n sigma0 g e)
  have hc := full_pair_replay S n s t e a hstop ha
  unfold BDL26AllDepthBottomComparisonStability.residual
  calc
    _ = e+(BDL26AllDepthBottomComparisonStability.correction S n s+
      BDL26AllDepthBottomComparisonStability.correction S n (perturbTop S n s e)) := by abel
    _ = e+(BDL26AllDepthBottomComparisonStability.correction S n t+
      BDL26AllDepthBottomComparisonStability.correction S n (perturbTop S n t e)) := by rw [hc]
    _ = _ := by abel
end QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse
