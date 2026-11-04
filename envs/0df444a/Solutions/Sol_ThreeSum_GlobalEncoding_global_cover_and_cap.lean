-- Prove2me | solution 1 for ThreeSum.GlobalEncoding.global_cover_and_cap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:03:39.569572+00:00
-- url     : https://prove2.me/submissions/8611ad0b-8de4-423c-ad1d-b333d96d9ed9

import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_Radix
import Mathlib.Data.List.OfFn
import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Theorems.Thm_ThreeSum_GlobalEncoding_representations_nonempty
import Theorems.Thm_ThreeSum_GlobalEncoding_representations_card_bound
import Definitions.Def_WeightedCache3SUM_Alias_322f8176f0ec5cb8
import Theorems.Thm_ThreeSum_Radix_representations_nonempty


set_option autoImplicit false
open ThreeSum ThreeSum.GlobalEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open LocalGraph LocalCoverBounds LocalHashMoments
namespace ThreeSum.GlobalEncoding
theorem _root_.solution {h : ℕ} (hh : 0 < h) (J : ℕ) (a b : ℤ) :
    (∃ xs : List (RetainedChoice h), xs.length = J ∧
      globalModulus h J ∣ a - Radix.positionalHash (localPrime h) rawLeft xs ∧
      globalModulus h J ∣ b - Radix.positionalHash (localPrime h) rawRight xs) ∧
      (representations h J a b).card ≤ representationCap h J := by
  obtain ⟨xs, hxs⟩ := representations_nonempty hh J a b
  exact ⟨⟨xs, (mem_representations h J a b xs).mp hxs⟩,
    representations_card_bound h J a b⟩
end ThreeSum.GlobalEncoding
