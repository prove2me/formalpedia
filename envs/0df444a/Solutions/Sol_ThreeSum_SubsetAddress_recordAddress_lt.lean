-- Prove2me | solution 1 for ThreeSum.SubsetAddress.recordAddress_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:08:38.486416+00:00
-- url     : https://prove2.me/submissions/660be18d-ff1d-4251-b7f4-d41a998154aa

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fin.Embedding
import Mathlib.Combinatorics.Colex
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Theorems.Thm_ThreeSum_SubsetAddress_subsetRank_lt

set_option autoImplicit false
open ThreeSum ThreeSum.SubsetAddress
set_option maxRecDepth 4000
open Finset
open scoped BigOperators
namespace ThreeSum.SubsetAddress
theorem _root_.solution {L cut : ℕ} {flags : Finset (Fin L)} {e : ℕ}
    (hflags : flags.card ≤ cut) (he : e ≤ L) :
    recordAddress flags e < downsetCap L cut * (L + 1) := by
  have hr := subsetRank_lt hflags
  have hp := Nat.mul_le_mul_right (L + 1) hr
  unfold recordAddress
  nlinarith
end ThreeSum.SubsetAddress
