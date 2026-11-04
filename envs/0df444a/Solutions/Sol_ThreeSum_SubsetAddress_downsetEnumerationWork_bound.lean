-- Prove2me | solution 1 for ThreeSum.SubsetAddress.downsetEnumerationWork_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:08:37.460723+00:00
-- url     : https://prove2.me/submissions/64390a77-1d78-432f-aefd-3015b03d48bf

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
import Theorems.Thm_ThreeSum_SubsetAddress_throughWork_bound

set_option autoImplicit false
open ThreeSum ThreeSum.SubsetAddress
set_option maxRecDepth 4000
open Finset
open scoped BigOperators
namespace ThreeSum.SubsetAddress
theorem _root_.solution (L cut : ℕ) :
    downsetEnumerationWork L cut ≤ (5 * L + 1) * downsetCap L cut + 2 * L + 1 := by
  have hw := throughWork_bound L (min cut L)
  have hk : min cut L ≤ L := min_le_right _ _
  unfold downsetEnumerationWork downsetCap
  nlinarith
end ThreeSum.SubsetAddress
