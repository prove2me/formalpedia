-- Prove2me | solution 1 for ThreeSum.StoredReporting.storedQuery_eq_prefixQuery
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:31:20.093047+00:00
-- url     : https://prove2.me/submissions/4061a558-ab72-4cf5-93a4-5272fda43c2a

import Definitions.Def_Submission_ThreeSum_BlockForced
import Definitions.Def_Submission_ThreeSum_StoredReporting
import Definitions.Def_WeightedCache3SUM_Alias_fdb051a7f9f9a8da

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
    storedQuery P d A B C a b c w k pre =
      prefixQuery (rawOn h J P d (A ×ˢ (B ×ˢ C)) a b c) w k pre := by
  rw [storedQuery, storedQueryValue_eq_prefixQuery P d A B C a b c w pre hk]
  exact Int.toNat_natCast _
end ThreeSum.StoredReporting
