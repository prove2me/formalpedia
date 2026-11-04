-- Prove2me | solution 1 for ThreeSum.SubsetAddress.IsMask.le_width
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:01:56.144339+00:00
-- url     : https://prove2.me/submissions/eef05774-33c1-43d8-b69b-1d8b98771253

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
import Theorems.Thm_ThreeSum_SubsetAddress_weight_le_width

set_option autoImplicit false
open ThreeSum ThreeSum.SubsetAddress
set_option maxRecDepth 4000
open Finset
open scoped BigOperators
namespace ThreeSum.SubsetAddress
namespace IsMask
theorem _root_.solution {L k m : ℕ} (hm : IsMask L k m) : k ≤ L := by
  rw [← hm.2]
  exact weight_le_width hm.1
end IsMask
end ThreeSum.SubsetAddress
