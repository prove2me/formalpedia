-- Prove2me | solution 1 for ThreeSum.StoredReporting.true_original_stored_reported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:13:37.750015+00:00
-- url     : https://prove2.me/submissions/2d5458d0-b79f-4c4b-b319-f0c6ebee4ea4

import Definitions.Def_Submission_ThreeSum_BlockForced
import Definitions.Def_Submission_ThreeSum_StoredReporting
import Theorems.Thm_ThreeSum_StoredReporting_storedFrontier_eq
import Theorems.Thm_ThreeSum_RawReporting_true_original_reported


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
theorem _root_.solution {h J : ℕ} {P d : ℤ}
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (hh : 0 < h) (hP : 0 < P)
    (t : Original α β γ) (ht : t ∈ A ×ˢ (B ×ˢ C)) (he : difference a b c t = 0) :
    ∃ r ∈ rawOn h J P d (A ×ˢ (B ×ˢ C)) a b c, r.1 = t ∧
      word r ∈ storedFrontier P d A B C a b c (wantedOf r) J := by
  obtain ⟨r, hr, hrt, hp⟩ := RawReporting.true_original_reported
    (A ×ˢ (B ×ˢ C)) a b c hh hP t ht he
  exact ⟨r, hr, hrt, (storedFrontier_eq P d A B C a b c (wantedOf r) le_rfl).symm ▸ hp⟩
end ThreeSum.StoredReporting
