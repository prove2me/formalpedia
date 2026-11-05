-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalMomentSourceProgram.host_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T12:17:10.392472+00:00
-- url     : https://prove2.me/submissions/8a67bc57-4ca3-4f75-b357-cef783305a9a

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_SourceCountHost
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentChannelStep
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryMomentSourceProgram
import Theorems.Thm_Light_Ends_append
import Theorems.Thm_Light_Exec_append
import Theorems.Thm_Light_Meets_append
import Theorems.Thm_ThreeSumApsp_AbsLe_append
import Theorems.Thm_ThreeSum_LightBalancedOffset_program_meets
import Theorems.Thm_ThreeSum_LightBandLookup_program_meets
import Theorems.Thm_ThreeSum_LightBlockCoefficients_program_meets
import Theorems.Thm_ThreeSum_LightBooleanDot_program_meets
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
import Theorems.Thm_ThreeSum_LightOutputDecodeDivide_program_meets
import Theorems.Thm_ThreeSum_LightRadixKeys_program_meets
import Theorems.Thm_ThreeSum_LightRadixRows_program_meets
import Theorems.Thm_ThreeSum_LightReportingAffine_program_meets
import Theorems.Thm_ThreeSum_LightResidueHistogram_program_meets
import Theorems.Thm_ThreeSum_LightScaleArray_program_meets
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_program_meets
import Theorems.Thm_ThreeSum_LightSourceResidues_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightTernaryOriginalJoin_program_meets
import Theorems.Thm_ThreeSum_LightTernaryParallelDictionaries_program_meets
import Theorems.Thm_ThreeSum_LightTernaryRank_program_meets
import Theorems.Thm_ThreeSum_LightTernarySourceHost_program_meets
import Theorems.Thm_ThreeSum_LightWantedJoin_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_631140e497667d8d
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightCacheEnumeration_program_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCost_program_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearEnumerationMain_program_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedSourceCountHost_program_meets


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalMomentSourceProgram
open Light TernaryWeightChannels
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalMomentSourceProgram
theorem _root_.solution {lim : Limits} {d TL TR TC keepLeft keepRight keepFront
    fbase gbase groups bank count dst k j : ℕ}
    (xl yl zl xr yr zr left right frontend : List ℤ) (μ : ℕ→ℤ)
    (F G : ℕ→ℕ→ℤ) (value : ℕ→ℤ)
    (hl : left.length=23) (hr : right.length=23) (hf : frontend.length=60)
    (hkeepRight : keepLeft≤keepRight) (hkeepFront : keepLeft≤keepFront)
    (hFend : fbase+groups*bank≤keepRight)
    (hleft : Meets lim (LightTernarySourceHost.program xl yl zl) 34 (d+1) left μ TL
      (fun _ ν => Kept μ ν keepLeft ∧ LightWeightedSourceCountHost.BankReads ν fbase groups bank F))
    (hright : ∀ ν, Kept μ ν keepLeft →
      Meets lim (LightTernarySourceHost.program xr yr zr) 34 (d+1) right ν TR
        (fun _ ξ => Kept ν ξ keepRight ∧ LightWeightedSourceCountHost.BankReads ξ gbase groups bank G))
    (hfrontend : ∀ ν, Kept μ ν keepLeft →
      LightWeightedSourceCountHost.BankReads ν fbase groups bank F →
      LightWeightedSourceCountHost.BankReads ν gbase groups bank G →
      Meets lim LightWeightedCountFrontend.program 63 (d+1) frontend ν TC
        (fun _ ξ => Kept ν ξ keepFront ∧ ∀ i<count, ξ (dst+i)=value i))
    (hd : d<lim.depth) :
    Meets lim (program xl yl zl xr yr zr k j) 134 d
      (LightWeightedSourceCountHost.args left right frontend) μ
      (LightWeightedSourceCountHost.time TL TR TC)
      (fun _ ν => Kept μ ν keepLeft ∧ ∀ i<count, ν (dst+i)=value i) := by
  exact (LightWeightedSourceCountHost.program_meets xl yl zl xr yr zr left right frontend μ
    F G value hl hr hf hkeepRight hkeepFront hFend hleft hright hfrontend hd).append (extra k j)
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalMomentSourceProgram
