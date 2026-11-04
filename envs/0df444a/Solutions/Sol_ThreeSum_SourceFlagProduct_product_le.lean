-- Prove2me | solution 1 for ThreeSum.SourceFlagProduct.product_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:17:07.181889+00:00
-- url     : https://prove2.me/submissions/5f55f1f3-d62c-4716-8767-2d5117dc66e2

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_SourceFlagProduct
import Theorems.Thm_ThreeSum_SourceFlagProduct_product_zero
import Theorems.Thm_ThreeSum_SourceFlagProduct_product_succ
attribute [local simp] ThreeSum.SourceFlagProduct.product_zero

set_option autoImplicit false
open ThreeSum ThreeSum.SourceFlagProduct
open Finset
open scoped BigOperators
namespace ThreeSum.SourceFlagProduct
theorem _root_.solution {n j : ℕ} (flag : ℕ → ℕ)
    (hflag : ∀ i < n, flag i ≤ 1) (hj : j ≤ n) : product flag j ≤ 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [product_succ]
    exact (Nat.mul_le_mul (ih (by omega)) (hflag j (by omega))).trans (by decide)
end ThreeSum.SourceFlagProduct
