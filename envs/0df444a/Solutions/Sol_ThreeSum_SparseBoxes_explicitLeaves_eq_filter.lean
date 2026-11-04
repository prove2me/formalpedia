-- Prove2me | solution 1 for ThreeSum.SparseBoxes.explicitLeaves_eq_filter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:42:05.454101+00:00
-- url     : https://prove2.me/submissions/81e1e54e-801c-42bf-af2c-cc17c50e6268

import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.ByContra
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_SparseBoxes
import Definitions.Def_WeightedCache3SUM_Alias_110f593934b92a01

set_option autoImplicit false
open ThreeSum ThreeSum.SparseBoxes
open scoped BigOperators
variable {α : Type*} [LinearOrder α]
namespace ThreeSum.SparseBoxes
theorem _root_.solution (q : Finset α) (t : ℕ) :
    explicitLeaves q t = q.powerset.filter (fun leaf => (q \ leaf).card < t) := by
  ext leaf
  simp only [mem_explicitLeaves, Finset.mem_filter, Finset.mem_powerset]
end ThreeSum.SparseBoxes
