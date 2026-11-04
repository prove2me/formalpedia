-- Prove2me | solution 1 for ThreeSum.Bands.interval_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:25:51.857247+00:00
-- url     : https://prove2.me/submissions/345ec7a8-17ed-45b2-892c-1ce9714794ae

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
theorem _root_.solution {lo hi : I → ℤ} (hs : Separated lo hi)
    {i j : I} {x : ℤ} (hi0 : lo i ≤ x) (hi1 : x ≤ hi i)
    (hj0 : lo j ≤ x) (hj1 : x ≤ hi j) : i = j := by
  by_contra hne
  rcases hs i j hne with h | h <;> omega
end ThreeSum.Bands
