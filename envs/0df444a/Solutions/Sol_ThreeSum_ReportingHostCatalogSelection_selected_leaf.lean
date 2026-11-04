-- Prove2me | solution 1 for ThreeSum.ReportingHostCatalogSelection.selected_leaf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:20:48.30322+00:00
-- url     : https://prove2.me/submissions/121a12ba-2253-42c0-a92a-5523cd73fb19

import Definitions.Def_Submission_ThreeSum_LightReportingCatalogIndex
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixQueryIndexed
import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogSelection
import Theorems.Thm_ThreeSum_ReportingHostPrefixCatalog_leftSource_eq
import Theorems.Thm_ThreeSum_ReportingHostPrefixCatalog_rightSource_eq


set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostCatalogSelection
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixCatalog ReportingHostPrefixOrder
open LightReportingPrefixCatalog LightReportingSuffixCatalog
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.ReportingHostCatalogSelection
theorem _root_.solution {h J k i : ℕ} (hk : k ≤ J)
    (P shift : ℤ) (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ)
    (o : Occurrences h J) (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (ho : outputOccurrences q = o)
    (hL : preL h J k i = leftPrefix k (prefixRows (J := J) pre))
    (hR : preR h J k i = rightPrefix k (outputRows q) (prefixRows (J := J) pre)) :
    leafWeight (block_fit hk) (leftSourceOf o P B b) (rightSourceOf o P shift C c)
      (suffixStage J (512*h) k) (preL h J k i) (preR h J k i) =
      LightReportingSuffixBoxes.localLeaf hk P shift B C b c q pre := by
  unfold LightReportingSuffixBoxes.localLeaf
  rw [hL,hR,leftSource_eq,rightSource_eq,ho]
  rfl
end ThreeSum.ReportingHostCatalogSelection
