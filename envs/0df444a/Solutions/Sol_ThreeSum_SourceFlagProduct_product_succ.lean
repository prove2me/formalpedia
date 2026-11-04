-- Prove2me | solution 1 for ThreeSum.SourceFlagProduct.product_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:13:13.117202+00:00
-- url     : https://prove2.me/submissions/7f145a58-f2dd-42e9-8da2-d3d8915136b2

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_SourceFlagProduct

set_option autoImplicit false
open ThreeSum ThreeSum.SourceFlagProduct
open Finset
open scoped BigOperators
namespace ThreeSum.SourceFlagProduct
theorem _root_.solution (flag : ℕ → ℕ) (n : ℕ) :
    product flag (n+1)=product flag n*flag n := Finset.prod_range_succ _ _
end ThreeSum.SourceFlagProduct
