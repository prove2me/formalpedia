-- Prove2me | solution 1 for ThreeSum.SubsetAddress.isMask_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:01:57.165304+00:00
-- url     : https://prove2.me/submissions/db7e548b-e253-4645-a80b-a305b6f310e1

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
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_SubsetAddress_weight_eq_zero_iff
attribute [local simp] ThreeSum.SubsetAddress.weight_zero

set_option autoImplicit false
open ThreeSum ThreeSum.SubsetAddress
set_option maxRecDepth 4000
open Finset
open scoped BigOperators
namespace ThreeSum.SubsetAddress
theorem _root_.solution (L m : ℕ) : IsMask L 0 m ↔ m = 0 := by
  constructor
  · intro hm
    exact (weight_eq_zero_iff hm.1).mp hm.2
  · rintro rfl
    exact ⟨Nat.two_pow_pos L, weight_zero L⟩
end ThreeSum.SubsetAddress
