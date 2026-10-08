-- Prove2me | solution 1 for ThreeSumApsp.Theorem21.exists_short_walk
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T07:52:48.99165+00:00
-- url     : https://prove2.me/submissions/53f17bcc-48f7-4aa6-9a3c-15a7313d4a6f

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

























/-- A walk with at least `n` edges visits some vertex twice: it consists of a walk `p`, a closed
walk `c` with at least one edge, and a walk `q`. -/
private theorem exists_closed_piece {n : ℕ} (i : Fin n) (rest : List (Fin n))
    (h : n ≤ rest.length) :
    ∃ p c q : List (Fin n),
      rest = p ++ c ++ q ∧ c ≠ [] ∧ walkEnd (walkEnd i p) c = walkEnd i p := by
  -- Among the `rest.length + 1` vertices that the walk visits, two are equal.
  obtain ⟨a, b, hab, hb, hrep⟩ : ∃ a b : ℕ, a < b ∧ b ≤ rest.length ∧
      walkEnd i (rest.take a) = walkEnd i (rest.take b) := by
    obtain ⟨a, b, hne, hrep⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun k : Fin (rest.length + 1) => walkEnd i (rest.take k)) (by simp; omega)
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · exact ⟨a, b, hlt, by omega, hrep⟩
    · exact ⟨b, a, hlt, by omega, hrep.symm⟩
  have htake : rest.take b = rest.take a ++ (rest.drop a).take (b - a) := by
    rw [← List.take_add, Nat.add_sub_cancel' hab.le]
  refine ⟨rest.take a, (rest.drop a).take (b - a), rest.drop b, ?_, ?_, ?_⟩
  · rw [← htake, List.take_append_drop]
  · refine List.ne_nil_of_length_pos ?_
    rw [List.length_take, List.length_drop]
    omega
  · rw [← walkEnd_append, ← htake, hrep]

/-- If no closed walk has negative weight, every walk can be replaced by a walk with the same ends,
fewer than `n` edges, no more edges than before, and no larger weight: cut out closed pieces. -/
theorem exists_short_walk_sourceProof {R : Type} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R] {n : ℕ}
    (w : Fin n → Fin n → WithTop R) (hw : NoNegativeCycle w) (i : Fin n) (rest : List (Fin n)) :
    ∃ rest' : List (Fin n), walkEnd i rest' = walkEnd i rest ∧ rest'.length < n ∧
      rest'.length ≤ rest.length ∧ walkWeight w i rest' ≤ walkWeight w i rest := by
  induction hlen : rest.length using Nat.strong_induction_on generalizing rest with
  | _ len ih =>
    rcases lt_or_ge rest.length n with hshort | hlong
    · exact ⟨rest, rfl, hshort, hlen.le, le_rfl⟩
    · -- The walk is `p`, then the closed walk `c`, then `q`; go on with `p`, then `q`.
      obtain ⟨p, c, q, rfl, hc, hclosed⟩ := exists_closed_piece i rest hlong
      have hend : walkEnd i (p ++ q) = walkEnd i (p ++ c ++ q) := by
        simp only [walkEnd_append, hclosed]
      have hweight : walkWeight w i (p ++ q) ≤ walkWeight w i (p ++ c ++ q) := by
        simp only [walkWeight_append, walkEnd_append, hclosed]
        gcongr
        exact le_add_of_nonneg_right (hw _ _ hclosed)
      have hless : (p ++ q).length < len := by
        have := List.length_pos_iff.mpr hc
        simp only [List.length_append] at hlen ⊢
        omega
      obtain ⟨rest', hend', hlt, hle, hweight'⟩ := ih _ hless (p ++ q) rfl
      exact ⟨rest', hend'.trans hend, hlt, by omega, hweight'.trans hweight⟩



















































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
    ∀ (i : Fin n) (rest : List.{0} (Fin n)),
      ∃ (rest' : List.{0} (Fin n)),
        And (@Eq.{1} (Fin n) (@ThreeSumApsp.walkEnd n i rest') (@ThreeSumApsp.walkEnd n i rest))
          (And (@LT.lt.{0} Nat instLTNat (@List.length.{0} (Fin n) rest') n)
            (And (@LE.le.{0} Nat instLENat (@List.length.{0} (Fin n) rest') (@List.length.{0} (Fin n) rest))
              (@LE.le.{0} (WithTop.{0} R)
                (@Preorder.toLE.{0} (WithTop.{0} R)
                  (@WithTop.instPreorder.{0} R
                    (@PartialOrder.toPreorder.{0} R
                      (@SemilatticeInf.toPartialOrder.{0} R
                        (@Lattice.toSemilatticeInf.{0} R
                          (@DistribLattice.toLattice.{0} R (@instDistribLatticeOfLinearOrder.{0} R inst_1)))))))
                (@ThreeSumApsp.walkWeight R
                  (@AddCommMagma.toAdd.{0} R
                    (@AddCommSemigroup.toAddCommMagma.{0} R
                      (@AddCommMonoid.toAddCommSemigroup.{0} R (@AddCommGroup.toAddCommMonoid.{0} R inst))))
                  (@NegZeroClass.toZero.{0} R
                    (@SubNegZeroMonoid.toNegZeroClass.{0} R
                      (@SubtractionMonoid.toSubNegZeroMonoid.{0} R
                        (@SubtractionCommMonoid.toSubtractionMonoid.{0} R
                          (@AddCommGroup.toDivisionAddCommMonoid.{0} R inst)))))
                  n w i rest')
                (@ThreeSumApsp.walkWeight R
                  (@AddCommMagma.toAdd.{0} R
                    (@AddCommSemigroup.toAddCommMagma.{0} R
                      (@AddCommMonoid.toAddCommSemigroup.{0} R (@AddCommGroup.toAddCommMonoid.{0} R inst))))
                  (@NegZeroClass.toZero.{0} R
                    (@SubNegZeroMonoid.toNegZeroClass.{0} R
                      (@SubtractionMonoid.toSubNegZeroMonoid.{0} R
                        (@SubtractionCommMonoid.toSubtractionMonoid.{0} R
                          (@AddCommGroup.toDivisionAddCommMonoid.{0} R inst)))))
                  n w i rest)))) := by
  exact @ThreeSumApsp.Theorem21.exists_short_walk_sourceProof

#print axioms solution
