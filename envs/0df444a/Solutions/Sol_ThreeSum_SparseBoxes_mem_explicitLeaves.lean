-- Prove2me | solution 1 for ThreeSum.SparseBoxes.mem_explicitLeaves
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:54:28.253174+00:00
-- url     : https://prove2.me/submissions/940d6217-03fd-4461-9f1d-41fc5ffdbe6a

import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Push


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

section


/-!
# Finite sparse-query boxes

The largest-missing-element partition and the reusable box recurrence are proved
here as exact finite identities.  The accompanying cardinalities concern the
actual canonical box family, not the family of all arbitrary free-coordinate
subsets.
-/

namespace ThreeSum.SparseBoxes

open scoped BigOperators

variable {α : Type*} [LinearOrder α]
























































































































































/-! ## Canonical free prefixes and the finite preprocessing family -/








































































































































































/-! ## The exact addition recurrence and query sum -/




































































































































































































/-! ## Number of query accesses -/




theorem mem_explicitLeaves_sourceProof (q leaf : Finset α) (t : ℕ) :
    leaf ∈ explicitLeaves q t ↔ leaf ⊆ q ∧ (q \ leaf).card < t := by
  constructor
  · intro hl
    obtain ⟨missing, hm, rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨j, hj, hmj⟩ := Finset.mem_biUnion.mp hm
    obtain ⟨hmq, hmc⟩ := Finset.mem_powersetCard.mp hmj
    refine ⟨Finset.sdiff_subset, ?_⟩
    rw [Finset.sdiff_sdiff_eq_self hmq, hmc]
    exact Finset.mem_range.mp hj
  · rintro ⟨hlq, hsmall⟩
    apply Finset.mem_image.mpr
    refine ⟨q \ leaf, ?_, Finset.sdiff_sdiff_eq_self hlq⟩
    exact Finset.mem_biUnion.mpr
      ⟨(q \ leaf).card, Finset.mem_range.mpr hsmall,
        Finset.mem_powersetCard.mpr ⟨Finset.sdiff_subset, rfl⟩⟩












































end ThreeSum.SparseBoxes

end

universe u_1

theorem solution : ∀ {α : Type u_1} [inst : LinearOrder.{u_1} α] (q leaf : Finset.{u_1} α) (t : Nat),
  Iff
    (@Membership.mem.{u_1, u_1} (Finset.{u_1} α) (Finset.{u_1} (Finset.{u_1} α))
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} (Finset.{u_1} α)) (Finset.{u_1} α)
        (@Finset.instSetLike.{u_1} (Finset.{u_1} α)))
      (@ThreeSum.SparseBoxes.explicitLeaves.{u_1} α inst q t) leaf)
    (And
      (@LE.le.{u_1} (Finset.{u_1} α)
        (@Preorder.toLE.{u_1} (Finset.{u_1} α)
          (@PartialOrder.toPreorder.{u_1} (Finset.{u_1} α) (@Finset.instPartialOrder.{u_1} α)))
        leaf q)
      (@LT.lt.{0} Nat instLTNat
        (@Finset.card.{u_1} α
          (@SDiff.sdiff.{u_1} (Finset.{u_1} α)
            (@Finset.instSDiff.{u_1} α fun (a b : α) => @LinearOrder.toDecidableEq.{u_1} α inst a b) q leaf))
        t)) := by
  exact @ThreeSum.SparseBoxes.mem_explicitLeaves_sourceProof

#print axioms solution
