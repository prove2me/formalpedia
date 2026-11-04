-- Prove2me | solution 1 for ThreeSum.SourceFlagProduct.product_eq_indicator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:01:08.325142+00:00
-- url     : https://prove2.me/submissions/bb070571-b90c-4126-9e8b-c67da657e9cf

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_SourceFlagProduct
import Theorems.Thm_ThreeSum_SourceFlagProduct_product_zero
import Theorems.Thm_ThreeSum_SourceFlagProduct_product_le
import Theorems.Thm_ThreeSum_SourceFlagProduct_product_eq_one_iff
attribute [local simp] ThreeSum.SourceFlagProduct.product_zero

set_option autoImplicit false
open ThreeSum ThreeSum.SourceFlagProduct
open Finset
open scoped BigOperators
namespace ThreeSum.SourceFlagProduct
theorem _root_.solution (flag : ℕ → ℕ) (n : ℕ) (p : Prop) [Decidable p]
    (hflag : ∀ i < n, flag i ≤ 1) (hp : (∀ i < n, flag i=1) ↔ p) :
    product flag n = if p then 1 else 0 := by
  have he := (product_eq_one_iff flag n).trans hp
  have hle := product_le flag hflag le_rfl
  by_cases hh : p
  · simp only [hh,ite_true]
    exact he.mpr hh
  · simp only [hh,ite_false]
    have hn : product flag n≠1 := fun h => hh (he.mp h)
    omega
end ThreeSum.SourceFlagProduct
