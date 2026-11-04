-- Prove2me | solution 1 for ThreeSum.Subset.zeta_forcedInput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:00:14.579859+00:00
-- url     : https://prove2.me/submissions/9e102a70-85ed-4046-920c-474afb77e176

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
import Definitions.Def_WeightedCache3SUM_Alias_cf48d5d5f60686aa

set_option autoImplicit false
open ThreeSum ThreeSum.Subset
open scoped BigOperators
variable {α : Type*} [DecidableEq α]
namespace ThreeSum.Subset
theorem _root_.solution
    (f : Finset α → ℤ) (pre suffix t : Finset α)
    (hd : Disjoint pre suffix) (ht : t ⊆ suffix) :
    zeta (forcedInput f pre suffix) t =
      partialZeta suffix f (pre ∪ t) := by
  rw [partialZeta_forced_prefix f suffix pre t hd ht]
  apply Finset.sum_congr rfl
  intro x hx
  have hxs := (Finset.mem_powerset.mp hx).trans ht
  simp only [forcedInput, hxs, ite_true]
end ThreeSum.Subset
