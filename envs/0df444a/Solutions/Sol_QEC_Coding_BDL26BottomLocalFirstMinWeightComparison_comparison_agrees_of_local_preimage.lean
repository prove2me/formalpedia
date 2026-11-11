-- Prove2me | solution 1 for QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.comparison_agrees_of_local_preimage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:17:12.836133+00:00
-- url     : https://prove2.me/submissions/bbd3685f-ff51-4779-80e3-96f5cdfcaf57

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
import Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_ownerFirstLookup_agrees_local
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_executableLocal_iff
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_executableSyndrome_eq
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_mem_allWords


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
open BDL26FiniteTannerSquare BDL26FiniteAlternatingCore BDL26DecodingGraph
open BDL26TannerLocalRegularity BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26ReplacementCochainMaps BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26LevelTwoDecoder
open scoped BigOperators
namespace QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
theorem _root_.solution (S : OddScale) (sigma : Syndrome S)
    (e : Error S) (he : levelTwoLocalError S e)
    (hs : tannerCoboundary1 (P2 S) e = sigma) :
    ownerFirstMinWeightFallback S sigma = decode S sigma := by
  unfold ownerFirstMinWeightFallback decode executableComparison executableDecode
  congr 1
  apply ownerFirstLookup_agrees_local
  refine ⟨toExecutableError S e,mem_allWords _ _,(executableLocal_iff S e).2 he,?_⟩
  rw [executableSyndrome_eq,hs]
end QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
