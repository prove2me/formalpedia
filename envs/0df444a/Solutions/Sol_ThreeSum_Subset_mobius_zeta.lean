-- Prove2me | solution 1 for ThreeSum.Subset.mobius_zeta
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:01:33.08459+00:00
-- url     : https://prove2.me/submissions/44ce2ced-f4a5-4387-adaa-ce1adb120556

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









theorem zeta_insert (f : Finset α → ℤ) {q : Finset α} {a : α}
    (ha : a ∉ q) :
    zeta f (insert a q) = zeta f q + zeta (fun s => f (insert a s)) q := by
  exact Finset.sum_powerset_insert ha f

theorem mobius_congr (q : Finset α) {f g : Finset α → ℤ}
    (h : ∀ s ⊆ q, f s = g s) : mobius f q = mobius g q := by
  apply Finset.sum_congr rfl
  intro s hs
  rw [h s (Finset.mem_powerset.mp hs)]

theorem mobius_add (f g : Finset α → ℤ) (q : Finset α) :
    mobius (fun s => f s + g s) q = mobius f q + mobius g q := by
  simp only [mobius, mul_add, Finset.sum_add_distrib]

theorem mobius_insert (f : Finset α → ℤ) {q : Finset α} {a : α}
    (ha : a ∉ q) :
    mobius f (insert a q) =
      mobius (fun s => f (insert a s)) q - mobius f q := by
  unfold mobius
  rw [Finset.sum_powerset_insert ha]
  have hleft :
      (∑ s ∈ q.powerset, (-1 : ℤ) ^ ((insert a q).card - s.card) * f s) =
      -(∑ s ∈ q.powerset, (-1 : ℤ) ^ (q.card - s.card) * f s) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    have hcard := Finset.card_le_card (Finset.mem_powerset.mp hs)
    have hexp : (insert a q).card - s.card = (q.card - s.card) + 1 := by
      rw [Finset.card_insert_of_notMem ha]
      omega
    rw [hexp, pow_succ]
    ring
  have hright :
      (∑ s ∈ q.powerset,
        (-1 : ℤ) ^ ((insert a q).card - (insert a s).card) * f (insert a s)) =
      ∑ s ∈ q.powerset, (-1 : ℤ) ^ (q.card - s.card) * f (insert a s) := by
    apply Finset.sum_congr rfl
    intro s hs
    have has : a ∉ s := fun h => ha ((Finset.mem_powerset.mp hs) h)
    rw [Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem has,
      Nat.add_sub_add_right]
  rw [hleft, hright]
  ring

/-- Exact Möbius inversion. The proof is induction on the finite output set. -/
theorem mobius_zeta_sourceProof (f : Finset α → ℤ) (q : Finset α) :
    mobius (zeta f) q = f q := by
  induction q using Finset.induction_on generalizing f with
  | empty => simp [mobius, zeta]
  | @insert a q ha ih =>
      rw [mobius_insert (zeta f) ha]
      have hchange :
          mobius (fun s => zeta f (insert a s)) q =
          mobius (fun s => zeta f s + zeta (fun t => f (insert a t)) s) q := by
        apply mobius_congr
        intro s hs
        exact zeta_insert f (fun h => ha (hs h))
      rw [hchange, mobius_add, ih f, ih (fun s => f (insert a s))]
      ring


























































































































































































/-! ## Stored partial zeta stages -/































































































































































































/-! ## Prefix reporting mass -/




























































end ThreeSum.Subset

end

universe u_1

theorem solution : ∀ {α : Type u_1} [DecidableEq.{u_1 + 1} α] (f : Finset.{u_1} α → Int) (q : Finset.{u_1} α),
  @Eq.{1} Int (@ThreeSum.Subset.mobius.{u_1} α (@ThreeSum.Subset.zeta.{u_1} α f) q) (f q) := by
  exact @ThreeSum.Subset.mobius_zeta_sourceProof

#print axioms solution
