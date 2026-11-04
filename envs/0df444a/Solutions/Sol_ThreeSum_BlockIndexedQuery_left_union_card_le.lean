-- Prove2me | solution 1 for ThreeSum.BlockIndexedQuery.left_union_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:53:28.548764+00:00
-- url     : https://prove2.me/submissions/c3156ba2-2598-41f0-952c-c3edc1538b00

import Definitions.Def_Submission_ThreeSum_BlockIndex
import Definitions.Def_Submission_ThreeSum_StoredReporting
import Definitions.Def_Submission_ThreeSum_SubsetTransport
import Definitions.Def_Submission_ThreeSum_SubsetStages
import Mathlib.Data.Fintype.Fin
import Definitions.Def_Submission_ThreeSum_BlockIndexedQuery
import Theorems.Thm_ThreeSum_BlockIndexedQuery_leftPrefix_disjoint_query
import Theorems.Thm_ThreeSum_BlockIndexedQuery_leftPrefix_card
import Theorems.Thm_ThreeSum_BlockIndexedQuery_querySet_card
namespace ThreeSum.BlockIndexedQuery
open Finset BlockRows BlockIndex BlockForced BlockEncoding GlobalEncoding
open LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open scoped BigOperators
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
private theorem sizes_le {J h k : ℕ} (hk : k ≤ J) : k*h+(J-k)*(2*h) ≤ 2*h*J := by
  calc
    _ ≤ k*(2*h)+(J-k)*(2*h) :=
      Nat.add_le_add_right (Nat.mul_le_mul_left k (by omega)) _
    _ = (k+(J-k))*(2*h) := (Nat.add_mul _ _ _).symm
    _ = _ := by rw [Nat.add_sub_of_le hk]; ring
section Histograms
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
end Histograms
end ThreeSum.BlockIndexedQuery
set_option autoImplicit false
open ThreeSum ThreeSum.BlockIndexedQuery
open Finset BlockRows BlockIndex BlockForced BlockEncoding GlobalEncoding
open LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open scoped BigOperators
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
namespace ThreeSum.BlockIndexedQuery
theorem _root_.solution {J L h k : ℕ} (hk : k ≤ J) (Q u : Fin J → Finset (Fin L))
    (hQ : ∀ i, (Q i).card = 2*h)
    (hu : ∀ i ∈ prefixIndices J k, (u i).card = h) :
    (leftPrefix k u ∪ querySet k Q).card ≤ 2*h*J := by
  rw [Finset.card_union_of_disjoint (leftPrefix_disjoint_query k Q u),
    leftPrefix_card hk u hu,querySet_card hk Q hQ]
  exact sizes_le hk
end ThreeSum.BlockIndexedQuery
