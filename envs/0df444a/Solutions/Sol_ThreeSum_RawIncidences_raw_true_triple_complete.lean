-- Prove2me | solution 1 for ThreeSum.RawIncidences.raw_true_triple_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:09:07.823877+00:00
-- url     : https://prove2.me/submissions/8247e3ba-9292-4bad-b744-4a1958afd0c8

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Definitions.Def_Submission_ThreeSum_Arithmetic
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FinCases
import Definitions.Def_Submission_ThreeSum_RawIncidences
import Theorems.Thm_ThreeSum_RawIncidences_raw_complete

set_option autoImplicit false
open ThreeSum ThreeSum.RawIncidences
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalCoverBounds
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.RawIncidences
theorem _root_.solution {h J : ℕ} {P d : ℤ} {T : Finset (Original α β γ)}
    {a : α → ℤ} {b : β → ℤ} {c : γ → ℤ} {t : Original α β γ}
    (hh : 0 < h) (hP : 0 < P) (ht : t ∈ T) (he : difference a b c t = 0) :
    ∃ r ∈ rawOn h J P d T a b c, r.1 = t :=
  raw_complete hh hP ht (by rw [he]; exact dvd_zero _)
end ThreeSum.RawIncidences
