-- Prove2me | solution 1 for SmallRatio.sum_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:15:16.284126+00:00
-- url     : https://prove2.me/submissions/fa363c1b-0448-4eae-bb22-ab5139f2eaa2

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Reciprocity

set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
namespace SmallRatio
theorem _root_.solution (m : ℕ) : ∑ j ∈ Ico 1 (m + 1), (2 * (j : ℤ) - 1) = (m : ℤ) ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_Ico_succ_top (by omega), ih]
    push_cast
    ring
end SmallRatio
