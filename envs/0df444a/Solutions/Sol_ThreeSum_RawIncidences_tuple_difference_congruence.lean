-- Prove2me | solution 1 for ThreeSum.RawIncidences.tuple_difference_congruence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:34:08.653164+00:00
-- url     : https://prove2.me/submissions/1858d5c7-b7f8-4429-92e4-1d10fe247b03

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Definitions.Def_Submission_ThreeSum_Arithmetic
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FinCases
import Definitions.Def_Submission_ThreeSum_RawIncidences
import Theorems.Thm_ThreeSum_RawIncidences_tupleKey_eq
import Theorems.Thm_ThreeSum_RawIncidences_tuple_mem_representations

set_option autoImplicit false
open ThreeSum ThreeSum.RawIncidences
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalCoverBounds
namespace ThreeSum.RawIncidences
theorem _root_.solution {h J : ℕ} {t : ChoiceTuple h J} {b c : ℤ}
    (ht : List.ofFn t ∈ representations h J b c) :
    globalModulus h J ∣ (c - b) - tupleKey t := by
  obtain ⟨hb, hc⟩ := (tuple_mem_representations t b c).mp ht
  rw [tupleKey_eq]
  rw [sub_sub_sub_comm]
  exact dvd_sub hc hb
end ThreeSum.RawIncidences
