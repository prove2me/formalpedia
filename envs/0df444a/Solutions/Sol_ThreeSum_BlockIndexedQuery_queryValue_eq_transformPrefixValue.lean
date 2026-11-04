-- Prove2me | solution 1 for ThreeSum.BlockIndexedQuery.queryValue_eq_transformPrefixValue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:51:40.649228+00:00
-- url     : https://prove2.me/submissions/12b58268-e2f1-42b8-896b-8d26ed874e00

import Definitions.Def_Submission_ThreeSum_BlockIndex
import Definitions.Def_Submission_ThreeSum_StoredReporting
import Definitions.Def_Submission_ThreeSum_SubsetTransport
import Definitions.Def_Submission_ThreeSum_SubsetStages
import Mathlib.Data.Fintype.Fin
import Definitions.Def_Submission_ThreeSum_BlockIndexedQuery
import Definitions.Def_WeightedCache3SUM_Alias_66e44d153b23210a
import Theorems.Thm_ThreeSum_SubsetTransport_mobius_partial_product_map


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
    (u : Fin J → Finset (Fin (512*h))) (hk : k ≤ J) :
    queryValue P d B C b c q k u =
      transformPrefixValue P d B C b c q (prefixIndices J k) u := by
  unfold queryValue SubsetStages.stageValue
  rw [← index_suffixDomain hk]
  exact SubsetTransport.mobius_partial_product_map (coordEquiv J (512*h)) _ _ _ _ _ _
end ThreeSum.BlockIndexedQuery
