-- Prove2me | solution 1 for ThreeSum.RawIncidences.witnesses_nonempty_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:06:04.658015+00:00
-- url     : https://prove2.me/submissions/93892ca9-7be9-45f0-afa6-4e1a2b24be30

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Definitions.Def_Submission_ThreeSum_Arithmetic
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FinCases
import Definitions.Def_Submission_ThreeSum_RawIncidences
import Theorems.Thm_ThreeSum_RawIncidences_witness_sound
import Theorems.Thm_ThreeSum_RawIncidences_witnesses_nonempty

set_option autoImplicit false
open ThreeSum ThreeSum.RawIncidences
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalCoverBounds
namespace ThreeSum.RawIncidences
theorem _root_.solution {h J : ℕ} {P d a b c : ℤ}
    (hh : 0 < h) (hP : 0 < P) (hguard : 4 * P ≤ globalModulus h J) :
    (witnesses h J P d a b c).Nonempty ↔ P ∣ c - b - a := by
  constructor
  · rintro ⟨w, hw⟩
    exact witness_sound hP hguard hw
  · exact witnesses_nonempty hh hP
end ThreeSum.RawIncidences
