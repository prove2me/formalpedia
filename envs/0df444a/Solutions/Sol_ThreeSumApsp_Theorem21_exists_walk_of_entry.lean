-- Prove2me | solution 1 for ThreeSumApsp.Theorem21.exists_walk_of_entry
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T07:52:48.30834+00:00
-- url     : https://prove2.me/submissions/75834fd9-6cd0-4c00-bf37-a5560eaa3545

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

/-- Every entry of the matrix after `t` squarings is the weight of a walk with at most `2^t` edges.
-/
theorem exists_walk_of_entry_sourceProof {R : Type} [AddCommGroup R] [LinearOrder R] {n : ℕ}
    (w : Fin n → Fin n → WithTop R) (t : ℕ) (i j : Fin n) :
    ∃ rest : List (Fin n), walkEnd i rest = j ∧ rest.length ≤ 2 ^ t ∧
      walkWeight w i rest = minPlusSquares w t i j := by
  induction t generalizing i j with
  | zero =>
    by_cases hij : i = j
    · subst hij
      exact ⟨[], rfl, by simp, by simp [walkWeight, minPlusSquares, weightMatrix]⟩
    · exact ⟨[j], rfl, by simp, by simp [walkWeight, minPlusSquares, weightMatrix, hij]⟩
  | succ t ih =>
    obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_inf Finset.univ ⟨i, Finset.mem_univ i⟩
      fun k => minPlusSquares w t i k + minPlusSquares w t k j
    obtain ⟨p, hpend, hplen, hpweight⟩ := ih i k
    obtain ⟨q, hqend, hqlen, hqweight⟩ := ih k j
    refine ⟨p ++ q, ?_, ?_, ?_⟩
    · rw [walkEnd_append, hpend, hqend]
    · rw [List.length_append, pow_succ]
      omega
    · rw [walkWeight_append, hpend, hpweight, hqweight]
      exact hk.symm



































































































end Theorem21









































end ThreeSumApsp

end


theorem solution : ∀ {R : Type} [inst : AddCommGroup.{0} R] [inst_1 : LinearOrder.{0} R] {n : Nat} (w : Fin n → Fin n → WithTop.{0} R)
  (t : Nat) (i j : Fin n),
  ∃ (rest : List.{0} (Fin n)),
    And (@Eq.{1} (Fin n) (@ThreeSumApsp.walkEnd n i rest) j)
      (And
        (@LE.le.{0} Nat instLENat (@List.length.{0} (Fin n) rest)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) t))
        (@Eq.{1} (WithTop.{0} R)
          (@ThreeSumApsp.walkWeight R
            (@AddCommMagma.toAdd.{0} R
              (@AddCommSemigroup.toAddCommMagma.{0} R
                (@AddCommMonoid.toAddCommSemigroup.{0} R (@AddCommGroup.toAddCommMonoid.{0} R inst))))
            (@NegZeroClass.toZero.{0} R
              (@SubNegZeroMonoid.toNegZeroClass.{0} R
                (@SubtractionMonoid.toSubNegZeroMonoid.{0} R
                  (@SubtractionCommMonoid.toSubtractionMonoid.{0} R
                    (@AddCommGroup.toDivisionAddCommMonoid.{0} R inst)))))
            n w i rest)
          (@ThreeSumApsp.minPlusSquares R
            (@AddCommMagma.toAdd.{0} R
              (@AddCommSemigroup.toAddCommMagma.{0} R
                (@AddCommMonoid.toAddCommSemigroup.{0} R (@AddCommGroup.toAddCommMonoid.{0} R inst))))
            (@NegZeroClass.toZero.{0} R
              (@SubNegZeroMonoid.toNegZeroClass.{0} R
                (@SubtractionMonoid.toSubNegZeroMonoid.{0} R
                  (@SubtractionCommMonoid.toSubtractionMonoid.{0} R
                    (@AddCommGroup.toDivisionAddCommMonoid.{0} R inst)))))
            inst_1 n w t i j))) := by
  exact @ThreeSumApsp.Theorem21.exists_walk_of_entry_sourceProof

#print axioms solution
