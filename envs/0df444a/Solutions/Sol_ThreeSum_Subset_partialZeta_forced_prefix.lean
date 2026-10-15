-- Prove2me | solution 1 for ThreeSum.Subset.partialZeta_forced_prefix
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:01:43.064732+00:00
-- url     : https://prove2.me/submissions/43341eb8-1fec-4c3d-907f-df12784fdd6b

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

section


/-!
# Exact subset identities used by the proposed 3SUM algorithm

This module proves the algebraic identities, rather than taking the claimed
algorithm or its running time as an assumption.  `zeta` is the ordinary finite
subset sum; `mobius` is its signed inverse.  The fixed-cardinality specialization
is the identity used by the repeated histogram construction.
-/

namespace ThreeSum.Subset

open scoped BigOperators

variable {α : Type*} [DecidableEq α]































































































































































































































































/-! ## Stored partial zeta stages -/






















































































/-- A forced pre is read from one entry of a stored suffix-zeta stage. -/
theorem partialZeta_forced_prefix_sourceProof
    (f : Finset α → ℤ) (processed s₀ t : Finset α)
    (hs : Disjoint s₀ processed) (ht : t ⊆ processed) :
    partialZeta processed f (s₀ ∪ t) =
      ∑ x ∈ t.powerset, f (s₀ ∪ x) := by
  have hnot : ∀ x ∈ s₀, x ∉ processed := fun x hx hy =>
    Finset.disjoint_left.mp hs hx hy
  have hi : (s₀ ∪ t) ∩ processed = t := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    aesop
  have hd : (s₀ ∪ t) \ processed = s₀ := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hx, hp⟩
      rcases hx with hxs | hxt
      · exact hxs
      · exact False.elim (hp (ht hxt))
    · intro hx
      exact ⟨Or.inl hx, hnot x hx⟩
  simp only [partialZeta, hi, hd]


















































































/-! ## Prefix reporting mass -/




























































end ThreeSum.Subset

end

universe u_1

theorem solution : ∀ {α : Type u_1} [inst : DecidableEq.{u_1 + 1} α] (f : Finset.{u_1} α → Int) (processed s₀ t : Finset.{u_1} α),
  @Disjoint.{u_1} (Finset.{u_1} α) (@Finset.instPartialOrder.{u_1} α) (@Finset.instOrderBot.{u_1} α) s₀ processed →
    @LE.le.{u_1} (Finset.{u_1} α)
        (@Preorder.toLE.{u_1} (Finset.{u_1} α)
          (@PartialOrder.toPreorder.{u_1} (Finset.{u_1} α) (@Finset.instPartialOrder.{u_1} α)))
        t processed →
      @Eq.{1} Int
        (@ThreeSum.Subset.partialZeta.{u_1} α inst processed f
          (@Union.union.{u_1} (Finset.{u_1} α) (@Finset.instUnion.{u_1} α inst) s₀ t))
        (∑ x ∈ @Finset.powerset.{u_1} α t,
          f (@Union.union.{u_1} (Finset.{u_1} α) (@Finset.instUnion.{u_1} α inst) s₀ x)) := by
  exact @ThreeSum.Subset.partialZeta_forced_prefix_sourceProof

#print axioms solution
