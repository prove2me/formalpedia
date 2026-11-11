-- Prove2me | solution 1 for QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.comparison_rightInverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:55:29.898858+00:00
-- url     : https://prove2.me/submissions/e21380d0-4763-453f-8d76-ed44874ef066

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
import Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_ownerFirstLookup_syndrome
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_executableSyndrome_eq
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_mem_allWords
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_toExecutableSyndrome_injective


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
    (hsigma : sigma ∈ LinearMap.range (tannerCoboundary1 (P2 S))) :
    tannerCoboundary1 (P2 S) (ownerFirstMinWeightFallback S sigma) = sigma := by
  apply toExecutableSyndrome_injective S
  rw [← executableSyndrome_eq]
  unfold ownerFirstMinWeightFallback
  rw [toExecutableError_toActualError]
  unfold executableComparison
  apply ownerFirstLookup_syndrome
  obtain ⟨e,he⟩ := hsigma
  exact ⟨toExecutableError S e,mem_allWords _ _,by rw [executableSyndrome_eq,he]⟩
end QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
