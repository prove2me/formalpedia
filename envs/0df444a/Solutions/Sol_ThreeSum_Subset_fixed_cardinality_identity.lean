-- Prove2me | solution 1 for ThreeSum.Subset.fixed_cardinality_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:11:09.151196+00:00
-- url     : https://prove2.me/submissions/49d6ec71-d6f8-4d36-9119-4822936d06bd

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
import Theorems.Thm_ThreeSum_Subset_mobius_zeta_product
import Definitions.Def_WeightedCache3SUM_Alias_645fa0f53a5987d6

set_option autoImplicit false
open ThreeSum ThreeSum.Subset
open scoped BigOperators
variable {α : Type*} [DecidableEq α]
namespace ThreeSum.Subset
theorem _root_.solution
    (f g : Finset α → ℤ) (q : Finset α) (a b : ℕ)
    (hf : ∀ s, f s ≠ 0 → s.card = a)
    (hg : ∀ v, g v ≠ 0 → v.card = b)
    (hq : q.card = a + b) :
    (∑ t ∈ q.powerset, (-1 : ℤ) ^ (q.card - t.card) *
      (∑ s ∈ t.powerset, f s) * (∑ v ∈ t.powerset, g v)) =
    ∑ s ∈ q.powerset, f s * g (q \ s) := by
  have h := mobius_zeta_product f g q
  rw [unionConvolution_eq_disjointConvolution f g q a b hf hg hq] at h
  simpa only [mobius, zeta, disjointConvolution, mul_assoc] using h
end ThreeSum.Subset
