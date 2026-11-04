-- Prove2me | solution 1 for ThreeSum.Subset.mobius_zeta_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:06:41.784306+00:00
-- url     : https://prove2.me/submissions/a7e14d39-696c-4bd2-b3dc-5995cefc82c8

import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ByContra
import Lean.Elab.Tactic.Omega
import Aesop
import Definitions.Def_Submission_ThreeSum_Subset
import Definitions.Def_WeightedCache3SUM_Alias_147fa6bb71e54b36
import Theorems.Thm_ThreeSum_Subset_zeta_unionConvolution

set_option autoImplicit false
open ThreeSum ThreeSum.Subset
open scoped BigOperators
variable {α : Type*} [DecidableEq α]
namespace ThreeSum.Subset
theorem _root_.solution (f g : Finset α → ℤ) (q : Finset α) :
    mobius (fun t => zeta f t * zeta g t) q = unionConvolution f g q := by
  have heq : (fun t => zeta f t * zeta g t) = zeta (unionConvolution f g) := by
    funext t
    exact (zeta_unionConvolution f g t).symm
  rw [heq, mobius_zeta]
end ThreeSum.Subset
