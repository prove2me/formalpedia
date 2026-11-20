-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoLocalBranchEndpoint.represented_global_success
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:55:36.067014+00:00
-- url     : https://prove2.me/submissions/2768fc9c-7b40-4986-b339-e4531e7e8ec7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoLocalBranchEndpoint
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_mem_allWords
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_search_complete
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoLocalBranchEndpoint
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26LevelTwoCode
open BDL26LevelTwoDistance BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open scoped BigOperators
open scoped Classical
namespace QEC.Coding.BDL26LevelTwoLocalBranchEndpoint
theorem _root_.solution (S : OddScale) (t : Syndrome S)
    (ht : ∃ e : Error S, delta S e=t) : ∃ w, globalSearch S t=some w := by
  obtain ⟨e,he⟩ := ht
  apply BDL26LevelTwoDecoder.search_complete
  refine ⟨BDL26LevelTwoDecoder.toExecutableError S e,
    BDL26LevelTwoDecoder.mem_allWords _ _,?_⟩
  apply decide_eq_true
  exact (encoded_delta S e).trans
    (congrArg (BDL26LevelTwoDecoder.toExecutableSyndrome S) he)
end QEC.Coding.BDL26LevelTwoLocalBranchEndpoint
