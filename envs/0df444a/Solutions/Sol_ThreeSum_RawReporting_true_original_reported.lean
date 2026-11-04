-- Prove2me | solution 1 for ThreeSum.RawReporting.true_original_reported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:11:13.971045+00:00
-- url     : https://prove2.me/submissions/80ac95d6-0f7e-4990-8510-1c5952953887

import Definitions.Def_Submission_ThreeSum_RawIncidences
import Definitions.Def_Submission_ThreeSum_Reporting
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Finset.Sort
import Definitions.Def_Submission_ThreeSum_RawReporting
import Theorems.Thm_ThreeSum_RawReporting_raw_word_reported
import Theorems.Thm_ThreeSum_RawIncidences_raw_true_triple_complete


set_option autoImplicit false
open ThreeSum ThreeSum.RawReporting
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.RawReporting
theorem _root_.solution {h J : ℕ} {P d : ℤ}
    (T : Finset (Original α β γ)) (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ)
    (hh : 0 < h) (hP : 0 < P) (t : Original α β γ) (ht : t ∈ T)
    (he : difference a b c t = 0) :
    ∃ r ∈ rawOn h J P d T a b c, r.1 = t ∧
      word r ∈ frontier (rawOn h J P d T a b c) (wantedOf r) J := by
  obtain ⟨r, hr, hrt⟩ := raw_true_triple_complete hh hP ht he
  exact ⟨r, hr, hrt, raw_word_reported _ r hr⟩
end ThreeSum.RawReporting
