-- Prove2me | solution 1 for ThreeSum.ReportingHostCatalogSelection.selected_box
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:26:23.036875+00:00
-- url     : https://prove2.me/submissions/261b92fa-6be4-4053-91fb-4c13c54e1531

import Definitions.Def_Submission_ThreeSum_LightReportingCatalogIndex
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixQueryIndexed
import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogSelection
import Theorems.Thm_ThreeSum_ReportingHostCatalogSelection_selected_leaf

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostCatalogSelection
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixCatalog ReportingHostPrefixOrder
open LightReportingPrefixCatalog LightReportingSuffixCatalog
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.ReportingHostCatalogSelection
theorem _root_.solution {μ : ℕ → ℤ} {h J k i boxCut boxBase : ℕ} (hk : k ≤ J)
    (P shift : ℤ) (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ)
    (o : Occurrences h J) (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (ho : outputOccurrences q = o)
    (hi : i < count h k)
    (hL : preL h J k i = leftPrefix k (prefixRows (J := J) pre))
    (hR : preR h J k i = rightPrefix k (outputRows q) (prefixRows (J := J) pre))
    (hboxes : ∀ j < count h k, LightBoxStages.StoredThrough μ
      (boxBase+j*stride (suffixStage J (512*h) k) boxCut) boxCut
      (leafWeight (block_fit hk) (leftSourceOf o P B b) (rightSourceOf o P shift C c)
        (suffixStage J (512*h) k) (preL h J k j) (preR h J k j))
      (suffixStage J (512*h) k)) :
    LightBoxStages.StoredThrough μ (boxBase+i*stride (suffixStage J (512*h) k) boxCut)
      boxCut (LightReportingSuffixBoxes.localLeaf hk P shift B C b c q pre)
      (suffixStage J (512*h) k) := by
  rw [← selected_leaf hk P shift B C b c o q pre ho hL hR]
  exact hboxes i hi
end ThreeSum.ReportingHostCatalogSelection
