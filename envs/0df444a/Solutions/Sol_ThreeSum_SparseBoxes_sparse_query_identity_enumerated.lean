-- Prove2me | solution 1 for ThreeSum.SparseBoxes.sparse_query_identity_enumerated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:19:18.384732+00:00
-- url     : https://prove2.me/submissions/092046b5-f66e-41cf-ba0a-4fcbd25126e5

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
import Definitions.Def_WeightedCache3SUM_Alias_16f3d07064c86bfa
import Theorems.Thm_ThreeSum_SparseBoxes_explicitLeaves_eq_filter

set_option autoImplicit false
open ThreeSum ThreeSum.SparseBoxes
open scoped BigOperators
variable {α : Type*} [LinearOrder α]
namespace ThreeSum.SparseBoxes
theorem _root_.solution (q : Finset α) (t : ℕ)
    (weight : Finset α → ℤ) :
    (∑ leaf ∈ q.powerset, weight leaf) =
      (∑ leaf ∈ explicitLeaves q t, weight leaf) +
      ∑ u ∈ q.powersetCard t, boxSum (q \ u) (queryFree q u) weight := by
  simpa only [explicitLeaves_eq_filter] using sparse_query_identity q t weight
end ThreeSum.SparseBoxes
