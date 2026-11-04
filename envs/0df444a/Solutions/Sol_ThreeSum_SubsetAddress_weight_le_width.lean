-- Prove2me | solution 1 for ThreeSum.SubsetAddress.weight_le_width
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:38:03.589604+00:00
-- url     : https://prove2.me/submissions/6b755668-4eaa-46a8-8590-e029f28fb64b

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
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
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
theorem _root_.solution {L m : ℕ} (hm : m < 2 ^ L) : weight L m ≤ L := by
  induction L generalizing m with
  | zero => simp [weight]
  | succ L ih =>
      rw [pow_two_succ] at hm
      by_cases hc : m < 2 ^ L
      · simpa [weight, hc] using (ih hc).trans (Nat.le_succ L)
      · have hr : m - 2 ^ L < 2 ^ L := by omega
        simpa [weight, hc] using Nat.succ_le_succ (ih hr)
end ThreeSum.SubsetAddress
