-- Prove2me | solution 1 for ThreeSum.RawIncidences.raw_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:43:19.465198+00:00
-- url     : https://prove2.me/submissions/89019d88-3d6c-49fb-9cdd-9f1da6f0cd26

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Definitions.Def_Submission_ThreeSum_Arithmetic
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FinCases
import Definitions.Def_Submission_ThreeSum_RawIncidences
import Theorems.Thm_ThreeSum_RawIncidences_witness_sound
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
    {a : α → ℤ} {b : β → ℤ} {c : γ → ℤ} {r : RawItem h J α β γ}
    (hP : 0 < P) (hguard : 4 * P ≤ globalModulus h J)
    (hr : r ∈ rawOn h J P d T a b c) : P ∣ difference a b c r.1 :=
  witness_sound hP hguard (mem_rawOn.mp hr).2
end ThreeSum.RawIncidences
