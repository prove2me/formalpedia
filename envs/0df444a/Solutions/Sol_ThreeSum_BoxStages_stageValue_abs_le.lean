-- Prove2me | solution 1 for ThreeSum.BoxStages.stageValue_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:10:47.996983+00:00
-- url     : https://prove2.me/submissions/e56f8a96-0127-4086-873b-e2c9a17b003b

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_ThreeSum_Subset_partialZeta_insert


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










theorem partialZeta_empty (f : Finset α → ℤ) (u : Finset α) :
    partialZeta ∅ f u = f u := by
  simp [partialZeta]








































































































/-- The ordinary zeta update also reads only from that same downset. -/
theorem zetaStep_stays_in_downset
    (u : Finset α) (a : α) (mu : ℕ) (h : u.card ≤ mu) :
    (u.erase a).card ≤ mu := by
  exact (Finset.card_le_card (Finset.erase_subset a u)).trans h





































































/-! ## Prefix reporting mass -/




























































end ThreeSum.Subset

end

section


/-!
# Canonical sparse boxes as stored prefix-zeta stages

A global coordinate prefix intersects each flagged set in an initial
segment. Storing those initialCoords stages uses only a polynomial factor more
than the compact downset. The resulting entries are exactly the signed
box sums used by the sparse-query partition.
-/

namespace ThreeSum.BoxStages

open Finset



@[simp] theorem mem_prefix {L j : ℕ} (a : Fin L) : a ∈ initialCoords L j ↔ a.val < j := by
  simp [initialCoords]

@[simp] theorem prefix_zero (L : ℕ) : initialCoords L 0 = ∅ := by
  ext a
  simp








theorem nextCoord_not_mem {L j : ℕ} (hj : j < L) : nextCoord j hj ∉ initialCoords L j := by
  simp [nextCoord]

theorem prefix_succ {L j : ℕ} (hj : j < L) :
    initialCoords L (j+1) = insert (nextCoord j hj) (initialCoords L j) := by
  ext a
  simp only [mem_prefix,Finset.mem_insert,Fin.ext_iff,nextCoord]
  omega




@[simp] theorem stageValue_zero {L : ℕ} (f : Finset (Fin L) → ℤ) : stageValue f 0 = f := by
  funext S
  simp [stageValue,Subset.partialZeta_empty]

theorem stageValue_succ {L j : ℕ} (f : Finset (Fin L) → ℤ) (hj : j < L) :
    stageValue f (j+1) = Subset.zetaStep (nextCoord j hj) (stageValue f j) := by
  funext S
  rw [stageValue,prefix_succ hj]
  exact Subset.partialZeta_insert f S (initialCoords L j) (nextCoord j hj) (nextCoord_not_mem hj)







theorem stageValue_abs_le_sourceProof {L cut U : ℕ} (f : Finset (Fin L) → ℤ)
    (hf : ∀ S, S.card ≤ cut → |f S| ≤ U) :
    ∀ j ≤ L, ∀ S, S.card ≤ cut → |stageValue f j S| ≤ ((2^j*U : ℕ) : ℤ) := by
  intro j
  induction j with
  | zero =>
    intro hj S hS
    simpa only [stageValue_zero,pow_zero,one_mul] using hf S hS
  | succ j ih =>
    intro hj S hS
    have hjL : j < L := by omega
    have h₁ := ih (by omega) S hS
    have h₂ := ih (by omega) (S.erase (nextCoord j hjL))
      (Subset.zetaStep_stays_in_downset S (nextCoord j hjL) cut hS)
    have hdouble : ((2^(j+1)*U : ℕ) : ℤ) =
        ((2^j*U : ℕ) : ℤ)+((2^j*U : ℕ) : ℤ) := by
      push_cast
      rw [pow_succ]
      ring
    rw [stageValue_succ f hjL,Subset.zetaStep,hdouble]
    split
    · exact (abs_add_le _ _).trans (add_le_add h₁ h₂)
    · exact h₁.trans (by have hn : (0 : ℤ) ≤ ((2^j*U : ℕ) : ℤ) := Int.natCast_nonneg _; omega)





































































end ThreeSum.BoxStages

end


theorem solution : ∀ {L cut U : Nat} (f : Finset.{0} (Fin L) → Int),
  (∀ (S : Finset.{0} (Fin L)),
      @LE.le.{0} Nat instLENat (@Finset.card.{0} (Fin L) S) cut →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (f S))
          (@Nat.cast.{0} Int instNatCastInt U)) →
    ∀ (j : Nat),
      @LE.le.{0} Nat instLENat j L →
        ∀ (S : Finset.{0} (Fin L)),
          @LE.le.{0} Nat instLENat (@Finset.card.{0} (Fin L) S) cut →
            @LE.le.{0} Int Int.instLEInt
              (@abs.{0} Int instLatticeInt Int.instAddGroup (@ThreeSum.BoxStages.stageValue L f j S))
              (@Nat.cast.{0} Int instNatCastInt
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)
                  U)) := by
  exact @ThreeSum.BoxStages.stageValue_abs_le_sourceProof

#print axioms solution
