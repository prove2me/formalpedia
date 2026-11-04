-- Prove2me | solution 1 for ThreeSum.SourceFlagProduct.product_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:56:52.519204+00:00
-- url     : https://prove2.me/submissions/4763ba7f-ee16-4871-af42-72a142bd9856

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
theorem _root_.solution (flag : ℕ → ℕ) (n : ℕ) :
    product flag n=1 ↔ ∀ i < n, flag i=1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [product_succ,mul_eq_one,ih]
    constructor
    · rintro ⟨hprev,hn⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact hprev i hi
      · exact hn
    · intro hall
      exact ⟨fun i hi => hall i (by omega),hall n (by omega)⟩
end ThreeSum.SourceFlagProduct
