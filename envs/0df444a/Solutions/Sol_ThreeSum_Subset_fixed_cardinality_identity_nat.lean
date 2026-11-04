-- Prove2me | solution 1 for ThreeSum.Subset.fixed_cardinality_identity_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:15:17.649329+00:00
-- url     : https://prove2.me/submissions/507d10f3-44a9-43d3-81c6-69d806d2bb78

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
import Theorems.Thm_ThreeSum_Subset_fixed_cardinality_identity

set_option autoImplicit false
open ThreeSum ThreeSum.Subset
open scoped BigOperators
variable {α : Type*} [DecidableEq α]
namespace ThreeSum.Subset
theorem _root_.solution
    (f g : Finset α → ℕ) (q : Finset α) (a b : ℕ)
    (hf : ∀ s, f s ≠ 0 → s.card = a)
    (hg : ∀ v, g v ≠ 0 → v.card = b)
    (hq : q.card = a + b) :
    (∑ t ∈ q.powerset, (-1 : ℤ) ^ (q.card - t.card) *
      (∑ s ∈ t.powerset, (f s : ℤ)) * (∑ v ∈ t.powerset, (g v : ℤ))) =
    (∑ s ∈ q.powerset, f s * g (q \ s) : ℕ) := by
  have hf' : ∀ s, (f s : ℤ) ≠ 0 → s.card = a := by
    intro s hs
    apply hf s
    intro hz
    apply hs
    simp only [hz, Nat.cast_zero]
  have hg' : ∀ v, (g v : ℤ) ≠ 0 → v.card = b := by
    intro v hv
    apply hg v
    intro hz
    apply hv
    simp only [hz, Nat.cast_zero]
  have hid := fixed_cardinality_identity
    (fun s => (f s : ℤ)) (fun v => (g v : ℤ)) q a b hf' hg' hq
  simpa only [Nat.cast_sum, Nat.cast_mul] using hid
end ThreeSum.Subset
