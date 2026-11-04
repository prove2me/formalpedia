-- Prove2me | solution 1 for ThreeSum.Bands.separated_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:28:03.525059+00:00
-- url     : https://prove2.me/submissions/9ef3ceb2-9b5e-4707-865d-cff80b578e82

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sets
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Bands

set_option autoImplicit false
open ThreeSum ThreeSum.Bands
variable {I J K : Type*}
namespace ThreeSum.Bands
theorem _root_.solution {lo hi : I → ℤ} (hs : Separated lo hi) (t : ℤ) :
    Separated (fun i => t + lo i) (fun i => t + hi i) := by
  intro i j hne
  change t + hi i < t + lo j ∨ t + hi j < t + lo i
  rcases hs i j hne with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)
end ThreeSum.Bands
