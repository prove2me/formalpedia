-- Prove2me | solution 1 for ThreeSum.BandPartition.covers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:16:32.484966+00:00
-- url     : https://prove2.me/submissions/fa43798d-200f-4d00-90ef-3230938a7d7e

import Definitions.Def_Submission_ThreeSum_BandEnumeration
import Definitions.Def_Submission_ThreeSum_BandPartition
import Theorems.Thm_ThreeSum_BandPartition_index_lt_size
import Theorems.Thm_ThreeSum_BandPartition_index_bounds

set_option autoImplicit false
open ThreeSum ThreeSum.BandPartition
namespace ThreeSum.BandPartition
theorem _root_.solution (f : ℕ → ℤ) (n g : ℕ) (hg : 0 < g)
    (hs : ∀ i j, i < j → j < n → f i < f j) {i : ℕ} (hi : i < n) :
    let A := family f n g hg hs
    A.lower (i/g) ≤ f i ∧ f i ≤ A.upper (i/g) := by
  have hb := index_bounds hg hi
  have hib := index_lt_size (g := g) hi
  exact ⟨monotone_of_strict hs hb.1 hi,
    monotone_of_strict hs (by omega) (stop_sub_one_lt hg hib)⟩
end ThreeSum.BandPartition
