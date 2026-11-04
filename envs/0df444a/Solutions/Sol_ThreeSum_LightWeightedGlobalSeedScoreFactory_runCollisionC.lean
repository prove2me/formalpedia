-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalSeedScoreFactory.runCollisionC
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T20:46:31.35893+00:00
-- url     : https://prove2.me/submissions/1d314904-443b-4bb3-8bf0-85703a8ac18f

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScore
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalDigitSpan
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchCount
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorFactoryScaled
import Definitions.Def_Submission_Weighted_Global_TernaryNativeTensorScore
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScoreFactory
import Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScoreFactory_BuiltO_transfer
import Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScoreFactory_Built_transfer
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_Need_Ok_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_Light_SolvedIn_mono
import Theorems.Thm_ThreeSum_LightBalancedOffset_program_meets
import Theorems.Thm_ThreeSum_LightBandLookup_program_meets
import Theorems.Thm_ThreeSum_LightBlockCoefficients_program_meets
import Theorems.Thm_ThreeSum_LightBooleanDot_program_meets
import Theorems.Thm_ThreeSum_LightCacheEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightCapacity_program_meets
import Theorems.Thm_ThreeSum_LightCyclic_program_meets
import Theorems.Thm_ThreeSum_LightFiniteTable_program_meets
import Theorems.Thm_ThreeSum_LightFixedRadixDictionary_program_meets
import Theorems.Thm_ThreeSum_LightKaratsuba_program_meets
import Theorems.Thm_ThreeSum_LightLookupSum_program_meets
import Theorems.Thm_ThreeSum_LightMaskBits_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightMaskHashes_program_meets
import Theorems.Thm_ThreeSum_LightModuloCounts_program_meets
import Theorems.Thm_ThreeSum_LightOneHot_program_meets
import Theorems.Thm_ThreeSum_LightOriginalOffset_program_meets
import Theorems.Thm_ThreeSum_LightOutputDecodeDigits_program_meets
import Theorems.Thm_ThreeSum_LightOutputDecodeDivide_program_meets
import Theorems.Thm_ThreeSum_LightRadixDigit_program_meets
import Theorems.Thm_ThreeSum_LightRadixKeys_program_meets
import Theorems.Thm_ThreeSum_LightRadixRows_program_meets
import Theorems.Thm_ThreeSum_LightReportingAffine_program_meets
import Theorems.Thm_ThreeSum_LightResidueHistogram_program_meets
import Theorems.Thm_ThreeSum_LightScaleArray_program_meets
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_program_meets
import Theorems.Thm_ThreeSum_LightSmallDivide_program_meets
import Theorems.Thm_ThreeSum_LightSourceResidues_key_lt
import Theorems.Thm_ThreeSum_LightSourceResidues_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightTernaryAppendKeys_key_lt
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightTernaryNearEnumerationMain_program_meets
import Theorems.Thm_ThreeSum_LightTernaryOriginalJoin_program_meets
import Theorems.Thm_ThreeSum_LightTernaryParallelDictionaries_program_meets
import Theorems.Thm_ThreeSum_LightTernaryPreparedState_Snapshot_transfer
import Theorems.Thm_ThreeSum_LightTernaryRank_program_meets
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_program_meets
import Theorems.Thm_ThreeSum_LightTernarySourceHost_program_meets
import Theorems.Thm_ThreeSum_LightTernaryWantedBatch_program_meets
import Theorems.Thm_ThreeSum_LightTernaryWantedCanonical_program_meets
import Theorems.Thm_ThreeSum_LightWantedJoin_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_631140e497667d8d
import Theorems.Thm_ThreeSum_LightWeightRow_program_meets
import Theorems.Thm_ThreeSum_LightWeightedCost_program_meets
import Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScore_program_meets
import Theorems.Thm_ThreeSum_LightWeightedNearEnumerationMain_program_meets
import Theorems.Thm_ThreeSum_LightWeightedPreparedState_Snapshot_transfer
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_program_meets


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalSeedScoreFactory
open Light
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {lim : Limits}
namespace ThreeSum.LightWeightedGlobalSeedScoreFactory
theorem _root_.solution {C : Config} [Fact C.p.Prime] {D : Data C} {depth R S cap V : ℕ}
    {raws : List ℤ} {words maps : List ℕ} {μ ν : ℕ → ℤ}
    (G : AppendGuard C D lim depth μ) (W : WantedGuard C D lim depth R S cap V raws words maps μ)
    (X : CollisionGuard C D lim R S raws words maps) (H : Built C D R S raws words maps μ ν) :
    Meets lim LightOriginalCollisionScore.program 0 (depth+1) [C.Cnew,C.nC,C.hist,C.power*C.p] ν
      (LightOriginalCollisionScore.time C.nC (C.power*C.p))
      (fun r ξ => r=D.collisionC ∧ Built C D R S raws words maps μ ξ) := by
  have hEnd : C.Cnew+C.nC≤C.hist := by
    have := G.CO; have := W.targetEnd; have := X.histogramAfter; omega
  have hh := LightOriginalCollisionScore.program_meets (d := depth+1) (src := C.Cnew)
    (n := C.nC) (hist := C.hist) (q := C.power*C.p) ν D.newC G.spaceWord
    (by have := X.histogramSpace; omega) X.histogramSpace (Or.inl hEnd) X.Cword
    (by intro i hi; exact LightTernaryAppendKeys.key_lt _ _ _ _ _ _ i (Fact.out : C.p.Prime).pos (G.oldCBound i hi))
    H.1.1.2 (by have := G.depth; omega)
  apply hh.mono le_rfl
  rintro r ξ ⟨hr,hCounts,hKeep⟩
  exact ⟨hr,H.transfer G W (fun x hx => hKeep x (Or.inl hx)) X.histogramAfter⟩
end ThreeSum.LightWeightedGlobalSeedScoreFactory
