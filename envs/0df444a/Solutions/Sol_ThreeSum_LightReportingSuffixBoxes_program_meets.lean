-- Prove2me | solution 1 for ThreeSum.LightReportingSuffixBoxes.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:34:47.789022+00:00
-- url     : https://prove2.me/submissions/a0f28a95-b06b-4d0f-afcc-7c8e97b7ea1e

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixSetup
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixBoxes
import Theorems.Thm_ThreeSum_LightReportingSuffixBoxes_residual_le_suffix
import Theorems.Thm_ThreeSum_BlockIndexedQuery_leftPrefix_card
import Theorems.Thm_ThreeSum_BlockIndexedQuery_leftPrefix_disjoint_query
import Theorems.Thm_ThreeSum_BlockIndexedQuery_leftSource_abs_le
import Theorems.Thm_ThreeSum_BlockIndexedQuery_left_union_card_le
import Theorems.Thm_ThreeSum_BlockIndexedQuery_querySet_card
import Theorems.Thm_ThreeSum_BlockIndexedQuery_rightPrefix_card
import Theorems.Thm_ThreeSum_BlockIndexedQuery_rightPrefix_disjoint_query
import Theorems.Thm_ThreeSum_BlockIndexedQuery_rightSource_abs_le
import Theorems.Thm_ThreeSum_BlockIndexedQuery_right_union_card_le
import Theorems.Thm_ThreeSum_BlockIndexedQuery_suffixStage_le
import Theorems.Thm_ThreeSum_BlockRows_mem_prefixIndices
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightBlockBoxes_program_meets
import Theorems.Thm_ThreeSum_LightBlockQuery_program_meets
import Theorems.Thm_ThreeSum_LightBlockQuery_sourceCut_le_width
import Theorems.Thm_ThreeSum_LightBoxStages_program_meets
import Theorems.Thm_ThreeSum_LightBoxSum_program_meets
import Theorems.Thm_ThreeSum_LightCanonicalBoxSum_program_meets
import Theorems.Thm_ThreeSum_LightDownsetAddress_program_meets
import Theorems.Thm_ThreeSum_LightDownsetSize_program_meets
import Theorems.Thm_ThreeSum_LightExplicitSum_program_meets
import Theorems.Thm_ThreeSum_LightLeafSum_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightMaskMinimum_program_meets
import Theorems.Thm_ThreeSum_LightMaskUnion_program_meets
import Theorems.Thm_ThreeSum_LightQueryBox_program_meets
import Theorems.Thm_ThreeSum_LightQueryEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightQueryWeights_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_c19df7a51d8d0351
import Theorems.Thm_ThreeSum_LightSign_program_meets
import Theorems.Thm_ThreeSum_LightSignedBoxSetup_program_meets
import Theorems.Thm_ThreeSum_LightSignedLeafGeneral_program_meets
import Theorems.Thm_ThreeSum_LightSignedLeafTable_program_meets
import Theorems.Thm_ThreeSum_LightSignedLeaf_program_meets
import Theorems.Thm_ThreeSum_LightSparseQuery_program_meets
import Theorems.Thm_ThreeSum_LightStageLookup_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightSubsetSetup_program_meets
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightZetaCell_program_meets
import Theorems.Thm_ThreeSum_LightZetaPass_program_meets
import Theorems.Thm_ThreeSum_LightZetaStages_program_meets
attribute [local simp] ThreeSum.BlockRows.mem_prefixIndices
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingSuffixBoxes
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds LightBlockQuery ReportingHostSuffix
variable {lim : Limits}
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.LightReportingSuffixBoxes
theorem _root_.solution {μ : ℕ → ℤ} {h J k baseL baseR boxCut boxBase maskBase work depth : ℕ}
    (pMod shift : ℤ) (B : Finset β) (C : Finset γ)
    (b : β → ℤ) (c : γ → ℤ) (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hk : k ≤ J) (hp : ValidPrefix q k pre)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hdataL : baseL+(width h J+1)*downsetCap (width h J) (sourceCut h J) ≤ boxBase)
    (hdataR : baseR+(width h J+1)*downsetCap (width h J) (sourceCut h J) ≤ boxBase)
    (hbox : boxBase+(suffixStage J (512*h) k+1)*downsetCap (suffixStage J (512*h) k) boxCut ≤ maskBase)
    (hmasks : maskBase+downsetCap (suffixStage J (512*h) k) boxCut ≤ work)
    (hspace : work+1+tableSize (width h J)+(width h J+1) ≤ lim.space)
    (hword : (((width h J+1)*2^(width h J+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : ((2^(suffixStage J (512*h) k)*
      ((2^(suffixStage J (512*h) k)*B.card)*(2^(suffixStage J (512*h) k)*C.card)) : ℕ) : ℤ) ≤ lim.word)
    (hboxCut : boxCut ≤ residualSize h J k)
    (hstoredL : LightZetaStages.StoredThrough μ baseL (sourceCut h J)
      (leftSource pMod B b q) (width h J))
    (hstoredR : LightZetaStages.StoredThrough μ baseR (sourceCut h J)
      (rightSource pMod shift C c q) (width h J))
    (hd : depth+width h J+11 ≤ lim.depth) :
    Meets lim LightReportingSuffixSetup.program 29 depth
      [width h J,sourceCut h J,boxCut,suffixStage J (512*h) k,k*h,
        subsetMask (leftPrefix k (prefixRows (J := J) pre)),k*h,
        subsetMask (rightPrefix k (outputRows q) (prefixRows (J := J) pre)),
        suffixStage J (512*h) k,k*(512*h),baseL,baseR,boxBase,maskBase,work]
      μ (LightReportingSuffixSetup.time (width h J) (suffixStage J (512*h) k) boxCut (k*(512*h)))
      (fun _ μ' =>
        LightBoxStages.StoredThrough μ' boxBase boxCut (localLeaf hk pMod shift B C b c q pre)
          (suffixStage J (512*h) k) ∧
        LightZetaStages.StoredThrough μ' baseL (sourceCut h J) (leftSource pMod B b q) (width h J) ∧
        LightZetaStages.StoredThrough μ' baseR (sourceCut h J) (rightSource pMod shift C c q) (width h J) ∧
        KeptBut μ μ' maskBase boxBase
          ((suffixStage J (512*h) k+1)*downsetCap (suffixStage J (512*h) k) boxCut)) := by
  have hQ : ∀ i, (outputRows q i).card = 2*h :=
    fun i => LayerCounts.mem_vertices.mp (q i).2.property
  have hu : ∀ i ∈ prefixIndices J k,
      prefixRows (J := J) pre i ⊆ outputRows q i ∧ (prefixRows (J := J) pre i).card = h := by
    intro i hi
    exact hp.2 i (mem_prefixIndices.mp hi)
  have hLc := leftPrefix_card hk (prefixRows (J := J) pre) (fun i hi => (hu i hi).2)
  have hRc := rightPrefix_card hk (outputRows q) (prefixRows (J := J) pre) hQ hu
  have hQc : (querySet k (outputRows q)).card = residualSize h J k := querySet_card hk _ hQ
  have hpreL : (leftPrefix k (prefixRows (J := J) pre)).card+boxCut ≤ sourceCut h J := by
    have hc := left_union_card_le hk (outputRows q) (prefixRows (J := J) pre) hQ (fun i hi => (hu i hi).2)
    rw [Finset.card_union_of_disjoint (leftPrefix_disjoint_query k _ _),hQc] at hc
    exact (Nat.add_le_add_left hboxCut _).trans hc
  have hpreR : (rightPrefix k (outputRows q) (prefixRows (J := J) pre)).card+boxCut ≤ sourceCut h J := by
    have hc := right_union_card_le hk (outputRows q) (prefixRows (J := J) pre) hQ hu
    rw [Finset.card_union_of_disjoint (rightPrefix_disjoint_query k _ _),hQc] at hc
    exact (Nat.add_le_add_left hboxCut _).trans hc
  have hm := LightReportingSuffixSetup.program_meets (d := depth) (μ := μ)
    (sourceCut := sourceCut h J) (block_fit hk)
    (leftPrefix k (prefixRows (J := J) pre))
    (rightPrefix k (outputRows q) (prefixRows (J := J) pre))
    (leftSource pMod B b q) (rightSource pMod shift C c q)
    hw (sourceCut_le_width h J) (hboxCut.trans residual_le_suffix) (suffixStage_le J (512*h) k)
    hdataL hdataR hbox hmasks hspace hword hvalueWord hpreL hpreR
    (fun S _ => leftSource_abs_le pMod B b q S)
    (fun S _ => rightSource_abs_le pMod shift C c q S) hstoredL hstoredR hd
  rw [hLc,hRc] at hm
  exact hm
end ThreeSum.LightReportingSuffixBoxes
