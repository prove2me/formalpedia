-- Prove2me | solution 1 for ThreeSum.SubsetAddress.weight_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:38:04.454622+00:00
-- url     : https://prove2.me/submissions/2c42d9c2-8fcd-4219-84b3-b9f34d51b2db

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

set_option autoImplicit false
open ThreeSum ThreeSum.SubsetAddress
set_option maxRecDepth 4000
open Finset
open scoped BigOperators
namespace ThreeSum.SubsetAddress
theorem _root_.solution {L m : ℕ} (hm : m < 2 ^ L) :
    weight L m = 0 ↔ m = 0 := by
  induction L generalizing m with
  | zero =>
      simp only [pow_zero] at hm
      have hz : m = 0 := by omega
      simp [hz, weight]
  | succ L ih =>
      by_cases hc : m < 2 ^ L
      · simpa [weight, hc] using ih hc
      · have hp := Nat.two_pow_pos L
        have hn : m ≠ 0 := by omega
        simp [weight, hc, hn]
end ThreeSum.SubsetAddress
