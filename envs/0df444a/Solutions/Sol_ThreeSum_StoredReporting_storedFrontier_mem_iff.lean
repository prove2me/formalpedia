-- Prove2me | solution 1 for ThreeSum.StoredReporting.storedFrontier_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:48:50.586406+00:00
-- url     : https://prove2.me/submissions/6958ab6e-aeab-4372-af0c-3423bc8e9d2a

import Definitions.Def_Submission_ThreeSum_BlockForced
import Definitions.Def_Submission_ThreeSum_StoredReporting
import Theorems.Thm_ThreeSum_StoredReporting_storedFrontier_eq
import Theorems.Thm_ThreeSum_RawReporting_mem_frontier_iff
import Definitions.Def_WeightedCache3SUM_Alias_c2dccdb99e31a4aa


set_option autoImplicit false
open ThreeSum ThreeSum.StoredReporting
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open BlockRows BlockEncoding BlockForced
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.StoredReporting
theorem _root_.solution {h J k : ℕ} (P d : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α)
    (pre : List (Finset (Fin (512 * h)))) (hk : k ≤ J) :
    pre ∈ storedFrontier P d A B C a b c w k ↔
      ∃ r ∈ rawOn h J P d (A ×ˢ (B ×ˢ C)) a b c,
        wantedOf r = w ∧ (word r).take k = pre := by
  rw [storedFrontier_eq P d A B C a b c w hk]
  exact RawReporting.mem_frontier_iff _ w hk pre
end ThreeSum.StoredReporting
