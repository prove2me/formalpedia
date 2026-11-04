-- Prove2me | solution 1 for ThreeSum.ReportingHostSuffix.original_query_local
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:50:27.471217+00:00
-- url     : https://prove2.me/submissions/d83aa899-5d8d-4a72-96ea-331c2d9df123

import Definitions.Def_Submission_ThreeSum_LightBlockBoxes
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffix
import Theorems.Thm_ThreeSum_ReportingHostSuffix_query_eq_local_signed_sum
import Theorems.Thm_ThreeSum_ReportingHostSuffix_lift_localQuery
import Theorems.Thm_ThreeSum_LightBlockQuery_queryValue_eq_prefixQuery


set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostSuffix
open Finset ThreeSum.SubsetAddress BlockIndexedQuery BlockRows BlockIndex BlockForced
open GlobalEncoding LocalCoverBounds StoredReporting LightBlockQuery
open scoped BigOperators
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
open RawIncidences RawReporting RawPrefixCounts
namespace ThreeSum.ReportingHostSuffix
theorem _root_.solution {h J k : ℕ} (pMod shift : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ)
    (w : Wanted h J α) (pre : List (Finset (Fin (512*h)))) (hk : k ≤ J)
    (hp : ValidPrefix w.2.2 k pre)
    (hkey : w.1 ∈ A ∧ globalModulus h J ∣
      (a w.1 % pMod+lift w.2.1*pMod+shift)-globalKey w.2.2) :
    (-1 : ℤ)^(localQuery hk (outputRows w.2.2)).card *
      ∑ S ∈ (localQuery hk (outputRows w.2.2)).powerset,
        leafWeight (block_fit hk) (leftSource pMod B b w.2.2) (rightSource pMod shift C c w.2.2)
          (suffixStage J (512*h) k) (leftPrefix k (prefixRows (J := J) pre))
          (rightPrefix k (outputRows w.2.2) (prefixRows (J := J) pre)) S =
      (prefixQuery (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w k pre : ℤ) := by
  rw [← query_eq_local_signed_sum,lift_localQuery]
  exact queryValue_eq_prefixQuery pMod shift A B C a b c w pre hk hp hkey
end ThreeSum.ReportingHostSuffix
