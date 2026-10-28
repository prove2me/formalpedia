-- Prove2me | solution 1 for ThreeBoundProfiles.sensitivity_le_diagonal_max
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-25T22:37:52.347067+00:00
-- url     : https://prove2.me/submissions/869657d8-6326-4639-b146-3c52f10a9fac

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Union
import Definitions.Def_Sensitivity213303_ProfileClosures

namespace OAI.Paper320
end OAI.Paper320
section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace ThreeBoundProfiles
end ThreeBoundProfiles
open ThreeBoundProfiles
open OAI.Paper320
open scoped Classical
variable {L I : Type} [Preorder L] [Fintype I]

/-- The two diagonal profile bounds bound global sensitivity. -/
theorem solution (F : L → (I → Bool) → Bool) (i : L) (a b : ℕ)
    (ha : ABound F i i a) (hb : BBound F i i b) : sensitivity (F i) ≤ max a b := by
  classical
  apply Finset.sup_le
  intro x _
  cases hx : F i x with
  | false =>
      have he : sensitivityAt (F i) x = (flipsTo (F i) true x).card := by
        simp [sensitivityAt, flipsTo, hx]
      rw [he]
      exact (ha x hx).trans (le_max_left _ _)
  | true =>
      have he : sensitivityAt (F i) x = (flipsTo (F i) false x).card := by
        simp [sensitivityAt, flipsTo, hx]
      rw [he]
      exact (hb x hx).trans (le_max_right _ _)
end
