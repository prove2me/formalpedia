-- Prove2me | solution 1 for ThreeSumApsp.eq_lowest_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T07:52:46.775917+00:00
-- url     : https://prove2.me/submissions/95d08e34-faf5-42c6-b976-11f7f46a5c69

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false



/-!
# Cubes and boxes (Section 4.2)

A cube is a string of `L` symbols, each of them one of the ten terms or a star, and its leaves are
obtained by replacing each star by any term. A box is a cube with at most `m - t` symbols `P₀` or
stars whose stars are all below its symbols `P₀`. This file proves what the paper says about cubes
and boxes before it turns to the boxes of one output string, in this order:

* from "Notions from Section 2": `M ≤ 10^L` (`M_le_ten_pow`);
* a cube with `e` stars has `10^e` leaves (`Cube.card_leaves`);
* the leaves, the stars and the symbols `P₀` of three cubes: a leaf read as a cube (`Cube.ofLeaf`),
  a cube with a star replaced by a term (`Cube.replace`), and a leaf with stars put at a set of
  levels (`Cube.starAt`); every cube that Section 4.2 makes from a leaf is of this third form;
* the leaves contributing to an output string `η` (w in the paper) are the leaves of the cube of `η`
  (`mem_leaves_cubeOf`), so the entry `(X_Q Y_Q)[η]` is the value of that cube
  (`mul_apply_eq_val_cubeOf`); Section 4.2 starts from this remark, and nothing else rests on it;
* the leaf obtained by replacing the stars of a cube with `P₀` chooses `P₀` where the cube has `P₀`
  or a star (`P0Levels_starsToP0`);
* a box only contains leaves of order at least `t` (`le_order_of_mem_leaves`);
* the `k` lowest levels of a set `S` lie below the other levels of `S` (`lowest_lt`), this property
  characterizes them (`eq_lowest_of_lt`), and there are `min k |S|` of them (`card_lowest`);
* a box is a leaf with its lowest symbols `P₀` replaced by stars (`eq_starLowest_starsToP0`), and
  every cube obtained in this way from a leaf with at most `m - t` symbols `P₀` is a box
  (`isBox_starLowest`).
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

variable {L : ℕ}








/-! ### Cubes and their leaves (Section 4.2) -/

























































/-! ### A leaf as a cube without stars (Section 4.2) -/
























/-! ### Replacing a star by a term (proof of Lemma 29) -/
































/-! ### Putting stars into a leaf (Section 4.2) -/




































/-! ### The cube of an output string (Section 4.2)

Section 4.2 starts from this remark. Nothing else rests on it. -/




























/-! ### Replacing the stars of a cube with `P₀` (proof of Lemma 29) -/






































/-! ### A box only contains leaves of order at least `t` (Section 4.2) -/


























/-! ### The `k` lowest levels of a set (Section 4.2) -/





/-- Membership in the set of the `k` lowest levels of `S`. -/
private lemma mem_lowest {k : ℕ} {S : Finset (Fin L)} {ℓ : Fin L} :
    ℓ ∈ lowest k S ↔ ℓ ∈ S ∧ (S.filter fun ℓ' => ℓ' < ℓ).card < k := by
  simp [lowest]



















/-- A subset `T` of `S` all of whose levels are below all the other levels of `S` consists of the
`|T|` lowest levels of `S`. -/
theorem eq_lowest_of_lt_sourceProof {S T : Finset (Fin L)} (hT : T ⊆ S)
    (h : ∀ ℓ ∈ T, ∀ ℓ' ∈ S \ T, ℓ < ℓ') : T = lowest T.card S := by
  ext ℓ
  rw [mem_lowest]
  constructor
  · -- The levels of `S` below a level `ℓ` of `T` are levels of `T` other than `ℓ`.
    refine fun hℓ => ⟨hT hℓ, card_lt_card ⟨fun x hx => ?_, fun hsub => ?_⟩⟩
    · by_contra hxT
      exact lt_asymm (mem_filter.1 hx).2 (h ℓ hℓ x (mem_sdiff.2 ⟨(mem_filter.1 hx).1, hxT⟩))
    · exact lt_irrefl ℓ (mem_filter.1 (hsub hℓ)).2
  · -- All of `T` is below a level of `S` outside `T`.
    rintro ⟨hℓS, hcard⟩
    by_contra hℓT
    refine absurd (card_le_card fun x hx => ?_) (not_le.2 hcard)
    exact mem_filter.2 ⟨hT hx, h x hx ℓ (mem_sdiff.2 ⟨hℓS, hℓT⟩)⟩






















/-! ### Replacing the lowest symbols `P₀` of a leaf by stars (Section 4.2 and the proof of Lemma 29)
-/










































end ThreeSumApsp

end


theorem solution : ∀ {L : Nat} {S T : Finset.{0} (Fin L)},
  @LE.le.{0} (Finset.{0} (Fin L))
      (@Preorder.toLE.{0} (Finset.{0} (Fin L))
        (@PartialOrder.toPreorder.{0} (Finset.{0} (Fin L)) (@Finset.instPartialOrder.{0} (Fin L))))
      T S →
    (∀ (ℓ : Fin L),
        @Membership.mem.{0, 0} (Fin L) (Finset.{0} (Fin L))
            (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin L)) (Fin L) (@Finset.instSetLike.{0} (Fin L))) T ℓ →
          ∀ (ℓ' : Fin L),
            @Membership.mem.{0, 0} (Fin L) (Finset.{0} (Fin L))
                (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin L)) (Fin L) (@Finset.instSetLike.{0} (Fin L)))
                (@SDiff.sdiff.{0} (Finset.{0} (Fin L)) (@Finset.instSDiff.{0} (Fin L) (instDecidableEqFin L)) S T) ℓ' →
              @LT.lt.{0} (Fin L) (@instLTFin L) ℓ ℓ') →
      @Eq.{1} (Finset.{0} (Fin L)) T (@ThreeSumApsp.lowest L (@Finset.card.{0} (Fin L) T) S) := by
  exact @ThreeSumApsp.eq_lowest_of_lt_sourceProof

#print axioms solution
