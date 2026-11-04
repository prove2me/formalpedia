-- Prove2me | solution 1 for ThreeSum.SubsetAddress.IsMask.succ_low
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:04:17.860228+00:00
-- url     : https://prove2.me/submissions/9998348d-6b03-4a46-b172-2d219d92581a

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
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
namespace ThreeSum.SubsetAddress
set_option maxRecDepth 4000
open Finset
open scoped BigOperators
private theorem pow_two_succ (L : ℕ) : 2 ^ (L + 1) = 2 ^ L + 2 ^ L := by
  rw [pow_succ]
  omega
end ThreeSum.SubsetAddress
set_option autoImplicit false
open ThreeSum ThreeSum.SubsetAddress
set_option maxRecDepth 4000
open Finset
open scoped BigOperators
namespace ThreeSum.SubsetAddress
namespace IsMask
theorem _root_.solution {L k m : ℕ} (hm : IsMask L k m) : IsMask (L + 1) k m := by
  have hb := hm.1
  refine ⟨?_, ?_⟩
  · rw [pow_two_succ]
    omega
  · simpa [weight, hm.1] using hm.2
end IsMask
end ThreeSum.SubsetAddress
