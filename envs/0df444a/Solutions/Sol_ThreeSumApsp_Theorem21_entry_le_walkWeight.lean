-- Prove2me | solution 1 for ThreeSumApsp.Theorem21.entry_le_walkWeight
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T07:52:47.478833+00:00
-- url     : https://prove2.me/submissions/81e40aad-de82-4ff2-9321-56b46ca89250

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false



/-!
# Theorem 21(b): repeated squaring computes the distances

For Theorem 21(b): if no closed walk has negative weight, then squaring the weight matrix `⌈log₂ n⌉`
times in the (min,+)-product yields the distance matrix, and all finite entries that occur have
absolute value at most `nU`, where `U` bounds the edge weights (`theorem_21b_repeated_squaring`,
`theorem_21b_entries_bounded`).

Under this hypothesis, after `t` squarings the entry at `(i, j)` is the least weight of a walk from
`i` to `j` with at most `2^t` edges: it is the weight of such a walk (`exists_walk_of_entry`) and at
most the weight of every such walk (`entry_le_walkWeight`).  Cutting closed pieces out of a walk
shows that fewer than `n` edges are enough (`exists_short_walk`), and a walk of finite weight with
`k` edges has weight at most `kU` in absolute value (`abs_walkWeight_le`).
-/

public section

namespace ThreeSumApsp

namespace Theorem21

/-- The end of a walk that is followed by a second walk. -/
private theorem walkEnd_append {n : ℕ} (i : Fin n) (p q : List (Fin n)) :
    walkEnd i (p ++ q) = walkEnd (walkEnd i p) q := by
  induction p generalizing i with
  | nil => rfl
  | cons j p ih => exact ih j

/-- The weight of a walk that is followed by a second walk is the sum of the two weights. -/
private theorem walkWeight_append {R : Type} [AddCommGroup R] {n : ℕ}
    (w : Fin n → Fin n → WithTop R) (i : Fin n) (p q : List (Fin n)) :
    walkWeight w i (p ++ q) = walkWeight w i p + walkWeight w (walkEnd i p) q := by
  induction p generalizing i with
  | nil => simp [walkWeight, walkEnd]
  | cons j p ih => simp [walkWeight, walkEnd, ih, add_assoc]









































































/-- If no closed walk has negative weight, the entry after `t` squarings is at most the weight of
every walk with at most `2^t` edges. -/
theorem entry_le_walkWeight_sourceProof {R : Type} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]
    {n : ℕ} (w : Fin n → Fin n → WithTop R) (hw : NoNegativeCycle w) (t : ℕ) (i : Fin n)
    (rest : List (Fin n)) (hlen : rest.length ≤ 2 ^ t) :
    minPlusSquares w t i (walkEnd i rest) ≤ walkWeight w i rest := by
  induction t generalizing i rest with
  | zero =>
    match rest, hlen with
    | [], _ => simp [walkWeight, walkEnd, minPlusSquares, weightMatrix]
    | [j], _ =>
      by_cases hij : i = j
      · -- The diagonal entry is 0, and a loop has weight at least 0.
        subst hij
        have h := hw i [i] rfl
        simpa [walkEnd, minPlusSquares, weightMatrix] using h
      · simp [walkWeight, walkEnd, minPlusSquares, weightMatrix, hij]
    | _ :: _ :: _, h => simp at h
  | succ t ih =>
    -- The walk is `p`, its first `2^t` edges, followed by `q`, the others.
    obtain ⟨p, q, rfl, hp, hq⟩ : ∃ p q, rest = p ++ q ∧ p.length ≤ 2 ^ t ∧ q.length ≤ 2 ^ t := by
      refine ⟨rest.take (2 ^ t), rest.drop (2 ^ t), (List.take_append_drop _ _).symm,
        List.length_take_le _ _, ?_⟩
      rw [List.length_drop]
      rw [pow_succ] at hlen
      omega
    rw [walkEnd_append, walkWeight_append]
    calc minPlusSquares w (t + 1) i (walkEnd (walkEnd i p) q)
        ≤ minPlusSquares w t i (walkEnd i p)
            + minPlusSquares w t (walkEnd i p) (walkEnd (walkEnd i p) q) :=
          Finset.inf_le (f := fun k =>
            minPlusSquares w t i k + minPlusSquares w t k (walkEnd (walkEnd i p) q))
            (Finset.mem_univ _)
      _ ≤ walkWeight w i p + walkWeight w (walkEnd i p) q := add_le_add (ih i p hp) (ih _ q hq)
















end Theorem21









































end ThreeSumApsp

end


theorem solution : ∀ {R : Type} [inst : AddCommGroup.{0} R] [inst_1 : LinearOrder.{0} R]
  [@IsOrderedAddMonoid.{0} R (@AddCommGroup.toAddCommMonoid.{0} R inst)
      (@PartialOrder.toPreorder.{0} R
        (@SemilatticeInf.toPartialOrder.{0} R
          (@Lattice.toSemilatticeInf.{0} R
            (@DistribLattice.toLattice.{0} R (@instDistribLatticeOfLinearOrder.{0} R inst_1)))))]
  {n : Nat} (w : Fin n → Fin n → WithTop.{0} R),
  @ThreeSumApsp.NoNegativeCycle R
      (@AddCommMagma.toAdd.{0} R
        (@AddCommSemigroup.toAddCommMagma.{0} R
          (@AddCommMonoid.toAddCommSemigroup.{0} R (@AddCommGroup.toAddCommMonoid.{0} R inst))))
      (@NegZeroClass.toZero.{0} R
        (@SubNegZeroMonoid.toNegZeroClass.{0} R
          (@SubtractionMonoid.toSubNegZeroMonoid.{0} R
            (@SubtractionCommMonoid.toSubtractionMonoid.{0} R (@AddCommGroup.toDivisionAddCommMonoid.{0} R inst)))))
      (@Preorder.toLE.{0} R
        (@PartialOrder.toPreorder.{0} R
          (@SemilatticeInf.toPartialOrder.{0} R
            (@Lattice.toSemilatticeInf.{0} R
              (@DistribLattice.toLattice.{0} R (@instDistribLatticeOfLinearOrder.{0} R inst_1))))))
      n w →
    ∀ (t : Nat) (i : Fin n) (rest : List.{0} (Fin n)),
      @LE.le.{0} Nat instLENat (@List.length.{0} (Fin n) rest)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) t) →
        @LE.le.{0} (WithTop.{0} R)
          (@Preorder.toLE.{0} (WithTop.{0} R)
            (@WithTop.instPreorder.{0} R
              (@PartialOrder.toPreorder.{0} R
                (@SemilatticeInf.toPartialOrder.{0} R
                  (@Lattice.toSemilatticeInf.{0} R
                    (@DistribLattice.toLattice.{0} R (@instDistribLatticeOfLinearOrder.{0} R inst_1)))))))
          (@ThreeSumApsp.minPlusSquares R
            (@AddCommMagma.toAdd.{0} R
              (@AddCommSemigroup.toAddCommMagma.{0} R
                (@AddCommMonoid.toAddCommSemigroup.{0} R (@AddCommGroup.toAddCommMonoid.{0} R inst))))
            (@NegZeroClass.toZero.{0} R
              (@SubNegZeroMonoid.toNegZeroClass.{0} R
                (@SubtractionMonoid.toSubNegZeroMonoid.{0} R
                  (@SubtractionCommMonoid.toSubtractionMonoid.{0} R
                    (@AddCommGroup.toDivisionAddCommMonoid.{0} R inst)))))
            inst_1 n w t i (@ThreeSumApsp.walkEnd n i rest))
          (@ThreeSumApsp.walkWeight R
            (@AddCommMagma.toAdd.{0} R
              (@AddCommSemigroup.toAddCommMagma.{0} R
                (@AddCommMonoid.toAddCommSemigroup.{0} R (@AddCommGroup.toAddCommMonoid.{0} R inst))))
            (@NegZeroClass.toZero.{0} R
              (@SubNegZeroMonoid.toNegZeroClass.{0} R
                (@SubtractionMonoid.toSubNegZeroMonoid.{0} R
                  (@SubtractionCommMonoid.toSubtractionMonoid.{0} R
                    (@AddCommGroup.toDivisionAddCommMonoid.{0} R inst)))))
            n w i rest) := by
  exact @ThreeSumApsp.Theorem21.entry_le_walkWeight_sourceProof

#print axioms solution
