-- Prove2me | solution 1 for ThreeSumApsp.lemma_29_split
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T08:03:56.394496+00:00
-- url     : https://prove2.me/submissions/0f24e184-8854-494a-93e9-795b1224e5a1

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













/-- Membership in the set of star levels of a cube. -/
@[simp]
theorem Cube.mem_starLevels {π : Cube L} {ℓ : Fin L} :
    ℓ ∈ Cube.starLevels π ↔ π ℓ = CubeSymbol.star := by
  simp [Cube.starLevels]

/-- Membership in the set of levels at which a cube has `P₀`. -/
@[simp]
theorem Cube.mem_P0Levels {π : Cube L} {ℓ : Fin L} :
    ℓ ∈ Cube.P0Levels π ↔ π ℓ = CubeSymbol.term Term.P0 := by
  simp [Cube.P0Levels]

































/-! ### A leaf as a cube without stars (Section 4.2) -/
























/-! ### Replacing a star by a term (proof of Lemma 29) -/

















/-- Replacing a star by a term removes its level from the star levels. -/
theorem Cube.starLevels_replace (π : Cube L) (ℓ : Fin L) (lam : Term) :
    Cube.starLevels (Cube.replace π ℓ lam) = (Cube.starLevels π).erase ℓ := by
  ext k
  by_cases hk : k = ℓ <;> simp [Cube.replace, hk]

/-- After a star is replaced by a term, the symbols `P₀` are at the old levels and possibly at the
level of that star. -/
theorem Cube.P0Levels_replace_subset (π : Cube L) (ℓ : Fin L) (lam : Term) :
    Cube.P0Levels (Cube.replace π ℓ lam) ⊆ insert ℓ (Cube.P0Levels π) := by
  intro k hk
  by_cases hkl : k = ℓ
  · exact mem_insert.2 (Or.inl hkl)
  · simpa [Cube.replace, hkl] using hk

/-! ### Putting stars into a leaf (Section 4.2) -/




































/-! ### The cube of an output string (Section 4.2)

Section 4.2 starts from this remark. Nothing else rests on it. -/




























/-! ### Replacing the stars of a cube with `P₀` (proof of Lemma 29) -/






































/-! ### A box only contains leaves of order at least `t` (Section 4.2) -/


























/-! ### The `k` lowest levels of a set (Section 4.2) -/



































































/-! ### Replacing the lowest symbols `P₀` of a leaf by stars (Section 4.2 and the proof of Lemma 29)
-/










































end ThreeSumApsp

end



/-!
# Lemma 29: the number of boxes, and their values (Section 4.3)

*The count* (`lemma_29_count`): there are at most `(m+1) ∑_{d=t}^{m} β_d` boxes. A box with `f`
symbols `P₀` or stars is a leaf with `f` symbols `P₀` in which the `e` lowest of them have been
turned into stars, for some `e ≤ f`. So these boxes correspond to the pairs of such a leaf and a
number `e ≤ f`, there are `(f+1) β_{m-f}` of them (`Lemma29.card_filter`), and we sum over
`f ≤ m - t`.

*The values* (`lemma_29_values`): the dynamic program `dpValue`, run on the two encodings of a tile,
returns the value of every box. This is an induction on the number of stars. The boxes without stars
are leaves (`Lemma29.no_stars`), and their values are products of two encoded numbers
(`Lemma29.val_ofLeaf`). Replacing the highest star of a box by the ten terms gives ten boxes with
one star fewer (`lemma_29_split`), whose values add up to the value of the box
(`Lemma29.recurrence`).
-/

public section

open Finset

namespace ThreeSumApsp






/-- Membership in the set of the boxes with `e` stars. -/
@[simp]
theorem mem_boxesWithStars {L m t e : ℕ} {π : Cube L} :
    π ∈ boxesWithStars L m t e ↔ IsBox m t π ∧ (Cube.starLevels π).card = e := by
  simp [boxesWithStars, boxes]

/-! ### The count -/







































































/-! ### The values -/






















/-- Proof of **Lemma 29**, "The values": "For a box π with e ≥ 1 stars, let ℓ be the highest
level at which π has a star. [...] each of these strings is again a box, with e - 1 stars."  The
strings are the `π[ℓ ← λ]`, and `e + 1` stands for the paper's `e`. -/
theorem lemma_29_split_sourceProof {L m t e : ℕ} {π : Cube L} (hπ : π ∈ boxesWithStars L m t (e + 1))
    (hne : (Cube.starLevels π).Nonempty) (lam : Term) :
    Cube.replace π ((Cube.starLevels π).max' hne) lam ∈ boxesWithStars L m t e := by
  obtain ⟨⟨hcount, hbelow⟩, hcard⟩ := mem_boxesWithStars.1 hπ
  have hstar : (Cube.starLevels (Cube.replace π ((Cube.starLevels π).max' hne) lam)).card = e := by
    rw [Cube.starLevels_replace, card_erase_of_mem (max'_mem _ hne), hcard,
      Nat.add_sub_cancel]
  have hP0 := Cube.P0Levels_replace_subset π ((Cube.starLevels π).max' hne) lam
  refine mem_boxesWithStars.2 ⟨⟨?_, fun k hk k' hk' => ?_⟩, hstar⟩
  · -- One star fewer (`hstar`, `hcard`) and at most one symbol `P₀` more (`hmore`), so (i) stays.
    have hmore := (card_le_card hP0).trans (card_insert_le _ _)
    omega
  · -- The new symbol is above the remaining stars, and so are the old symbols `P₀`, by (ii).
    rw [Cube.starLevels_replace, mem_erase] at hk
    rcases mem_insert.1 (hP0 hk') with hnew | hold
    · exact hnew ▸ lt_of_le_of_ne (le_max' _ k hk.2) hk.1
    · exact hbelow k hk.2 k' hold



































end ThreeSumApsp

end


theorem solution : ∀ {L m t e : Nat} {π : ThreeSumApsp.Cube L},
  @Membership.mem.{0, 0} (ThreeSumApsp.Cube L) (Finset.{0} (ThreeSumApsp.Cube L))
      (@SetLike.instMembership.{0, 0} (Finset.{0} (ThreeSumApsp.Cube L)) (ThreeSumApsp.Cube L)
        (@Finset.instSetLike.{0} (ThreeSumApsp.Cube L)))
      (ThreeSumApsp.boxesWithStars L m t
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) e
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      π →
    ∀ (hne : @Finset.Nonempty.{0} (Fin L) (@ThreeSumApsp.Cube.starLevels L π)) (lam : ThreeSumApsp.Term),
      @Membership.mem.{0, 0} (ThreeSumApsp.Cube L) (Finset.{0} (ThreeSumApsp.Cube L))
        (@SetLike.instMembership.{0, 0} (Finset.{0} (ThreeSumApsp.Cube L)) (ThreeSumApsp.Cube L)
          (@Finset.instSetLike.{0} (ThreeSumApsp.Cube L)))
        (ThreeSumApsp.boxesWithStars L m t e)
        (@ThreeSumApsp.Cube.replace L π
          (@Finset.max'.{0} (Fin L) (@Fin.instLinearOrder L) (@ThreeSumApsp.Cube.starLevels L π) hne) lam) := by
  exact @ThreeSumApsp.lemma_29_split_sourceProof

#print axioms solution
