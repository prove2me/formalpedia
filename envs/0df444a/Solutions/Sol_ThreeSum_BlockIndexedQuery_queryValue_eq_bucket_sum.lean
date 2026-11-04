-- Prove2me | solution 1 for ThreeSum.BlockIndexedQuery.queryValue_eq_bucket_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:48:55.914343+00:00
-- url     : https://prove2.me/submissions/bd80e1d5-6e67-4d9c-949c-f7825c0ce146

import Definitions.Def_Submission_ThreeSum_BlockIndex
import Definitions.Def_Submission_ThreeSum_StoredReporting
import Definitions.Def_Submission_ThreeSum_SubsetTransport
import Definitions.Def_Submission_ThreeSum_SubsetStages
import Mathlib.Data.Fintype.Fin
import Definitions.Def_Submission_ThreeSum_BlockIndexedQuery
import Theorems.Thm_ThreeSum_BlockIndexedQuery_queryValue_eq_transformPrefixValue
import Definitions.Def_WeightedCache3SUM_Alias_bfbfce5ef1eaf3a6


set_option autoImplicit false
open ThreeSum ThreeSum.BlockIndexedQuery
open Finset BlockRows BlockIndex BlockForced BlockEncoding GlobalEncoding
open LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open scoped BigOperators
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.BlockIndexedQuery
theorem _root_.solution {h J k : ℕ} (P d : ℤ)
    (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ) (q : GlobalOutput h J)
    (u : Fin J → Finset (Fin (512*h))) (hk : k ≤ J)
    (hu : ∀ i ∈ prefixIndices J k, u i ⊆ outputRows q i ∧ (u i).card = h) :
    queryValue P d B C b c q k u =
      (∑ t ∈ completedTuples q (prefixIndices J k) u,
        leftBucket P B b t * rightBucket P d C c t : ℕ) := by
  rw [queryValue_eq_transformPrefixValue P d B C b c q u hk]
  exact transformPrefixValue_eq_bucket_sum P d B C b c q _ u hu
end ThreeSum.BlockIndexedQuery
