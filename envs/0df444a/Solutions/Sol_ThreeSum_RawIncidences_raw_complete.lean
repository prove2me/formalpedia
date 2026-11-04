-- Prove2me | solution 1 for ThreeSum.RawIncidences.raw_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:05:55.416603+00:00
-- url     : https://prove2.me/submissions/0e772110-3130-477b-bc43-5760024d36a0

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Definitions.Def_Submission_ThreeSum_Arithmetic
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FinCases
import Definitions.Def_Submission_ThreeSum_RawIncidences
import Theorems.Thm_ThreeSum_RawIncidences_witnesses_nonempty
import Theorems.Thm_ThreeSum_RawIncidences_mem_rawOn

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
    (hh : 0 < h) (hP : 0 < P) (ht : t ∈ T) (hd : P ∣ difference a b c t) :
    ∃ r ∈ rawOn h J P d T a b c, r.1 = t := by
  obtain ⟨w, hw⟩ := witnesses_nonempty hh hP hd
  exact ⟨⟨t, w⟩, mem_rawOn.mpr ⟨ht, hw⟩, rfl⟩
end ThreeSum.RawIncidences
