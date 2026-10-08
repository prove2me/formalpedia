-- Prove2me | solution 1 for ThreeSumApsp.sec2_card_contributing_of_order
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T08:03:57.145076+00:00
-- url     : https://prove2.me/submissions/9f977354-b52b-4d71-a4ea-6ffbdb62cc56

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
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
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
# Cardinalities of finite sets

General facts about finite sets.

* A product with one value on `S` and another elsewhere (`Finset.prod_ite_mem_const`); two products
  that vanish unless one set lies in another (`Finset.prod_ite_ite_subset`,
  `Finset.prod_ite_ite_superset`); the number of sets of `k` elements inside a set or around a set
  (`Finset.sum_powersetCard_ite_subset`, `Finset.card_powersetCard_superset`).
* At most `c` elements of a set have a given quotient by `c` under an injective function
  (`Finset.card_filter_div_eq_le`).
* A finite subset of `Fin L` has `j` elements below its `j`-th lowest element
  (`Finset.card_filter_lt_orderEmbOfFin`, from `Finset.card_filter_lt_map` for any increasing
  sequence).

* A function `f : ι → α` has a property `p` at the place `i` if `p (f i)` holds. The number of
  functions `f` with `f i ∈ A i` that have `p` exactly at the places of a set `S` is a product over
  the places (`Finset.card_pi_places_eq`). The number of those that have `p` at exactly `k` places
  is the sum of these products over the sets `S` of `k` places (`Finset.card_pi_places_card`).
  Without the restriction to `A` it is a binomial coefficient times two powers
  (`Finset.card_places_card`).
-/

public section

namespace Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A product that takes the value `a` on `S` and `b` elsewhere. -/
theorem prod_ite_mem_const {M : Type*} [CommMonoid M] (S : Finset ι) (a b : M) :
    (∏ i, if i ∈ S then a else b) = a ^ #S * b ^ (Fintype.card ι - #S) := by
  rw [prod_ite, prod_const, prod_const, filter_mem_eq_inter, univ_inter, filter_not,
    filter_mem_eq_inter, univ_inter, ← compl_eq_univ_sdiff, card_compl]

/-- A product with the factors `1` on `S ∩ Q`, `0` on `S \ Q`, `c` on `Q \ S` and `1` elsewhere: it
is `0` unless `S ⊆ Q`. -/
theorem prod_ite_ite_subset {M : Type*} [CommMonoidWithZero M] (Q S : Finset ι) (c : M) :
    (∏ i, if i ∈ S then (if i ∈ Q then 1 else 0) else (if i ∈ Q then c else 1))
      = if S ⊆ Q then c ^ (#Q - #S) else 0 := by
  split_ifs with h
  · have hterm : ∀ i, (if i ∈ S then (if i ∈ Q then 1 else 0) else (if i ∈ Q then c else 1))
        = if i ∈ Q \ S then c else 1 := fun i => by
      by_cases hS : i ∈ S
      · simp [hS, h hS]
      · simp [hS]
    simp_rw [hterm]
    rw [prod_ite_mem_const, one_pow, mul_one, card_sdiff_of_subset h]
  · obtain ⟨i, hiS, hiQ⟩ := not_subset.mp h
    exact prod_eq_zero (mem_univ i) (by simp [hiS, hiQ])













/-- The number of sets of `k` elements inside `Q`, each counted `c` times. -/
theorem sum_powersetCard_ite_subset (Q : Finset ι) (k c : ℕ) :
    (∑ S ∈ powersetCard k (univ : Finset ι), if S ⊆ Q then c else 0) = (#Q).choose k * c := by
  rw [← sum_filter, sum_const, smul_eq_mul, ← card_powersetCard]
  congr 2
  ext S
  simp [mem_powersetCard, and_comm]





























/-! ## The elements below a bound -/















/-! ## Functions by the set of places with a property -/

variable {α : Type*} [Fintype α]

/-- The number of functions `f` with `f i ∈ A i` whose set of places with `p` is exactly `S`: choose
a value with `p` at each place of `S` and one without `p` at every other place. -/
theorem card_pi_places_eq [DecidableEq α] (A : ι → Finset α) (p : α → Prop) [DecidablePred p]
    (S : Finset ι) :
    #{f : ι → α | (∀ i, f i ∈ A i) ∧ ({i | p (f i)} : Finset ι) = S} =
      ∏ i, if i ∈ S then #{a ∈ A i | p a} else #{a ∈ A i | ¬ p a} := by
  have hmem (i : ι) (x : α) : (x ∈ if i ∈ S then {a ∈ A i | p a} else {a ∈ A i | ¬ p a}) ↔
      x ∈ A i ∧ (p x ↔ i ∈ S) := by
    split_ifs with hi <;> simp [hi]
  simp_rw [← apply_ite Finset.card, ← Fintype.card_piFinset]
  congr 1
  ext f
  simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, hmem, forall_and,
    Finset.ext_iff]

/-- The number of functions `f` with `f i ∈ A i` that have `p` at exactly `k` places, as a sum over
the possible sets of these places. -/
theorem card_pi_places_card [DecidableEq α] (A : ι → Finset α) (p : α → Prop) [DecidablePred p]
    (k : ℕ) :
    #{f : ι → α | (∀ i, f i ∈ A i) ∧ #{i | p (f i)} = k} =
      ∑ S ∈ powersetCard k (univ : Finset ι),
        ∏ i, if i ∈ S then #{a ∈ A i | p a} else #{a ∈ A i | ¬ p a} := by
  rw [card_eq_sum_card_fiberwise (f := fun f : ι → α => ({i | p (f i)} : Finset ι))
    (t := powersetCard k (univ : Finset ι))
    fun f hf => mem_coe.2 (mem_powersetCard.2 ⟨subset_univ _, (mem_filter.1 hf).2.2⟩)]
  refine sum_congr rfl fun S hS => ?_
  rw [← card_pi_places_eq, filter_filter]
  exact congrArg card (filter_congr fun f _ =>
    ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2 ▸ (mem_powersetCard.1 hS).2⟩, h.2⟩⟩)












end Finset

end



/-!
# Section 2.4.3, first half: the orders of the leaves and equation (5)

A leaf that contributes to an output string with inner set `Q` is free at the `m` levels of `Q` and
fixed at the other levels.  Its order is `m` minus the number of levels at which it chooses `P₀`.

* One level.  A term contributes to `z` exactly if `z = z₀` or the term is the private term of `z`
  (`Term.contributes_iff`), so a leaf contributing to a string chooses `P₀` only at levels of the
  inner set (`P0Levels_subset`).  The numbers of terms of each kind that contribute to a variable,
  and of variables of each kind to which a term contributes, are read off the ten terms.
* Counts.  `10^m` leaves contribute to a string: ten terms for each level of `Q`
  (`card_filter_contributes`).  The other counts sort strings by the set of levels at which they
  have a letter of a given kind (`Finset.card_pi_places_card`, `Finset.card_places_card`): `α_d` of
  the leaves contributing to a string have order `d` (`sec2_card_contributing_of_order`), the whole
  tree has `β_d` leaves of order `d` (`card_filter_order_eq`), with `β₀ = M` (`beta_zero_eq_M`), and
  a leaf of order `d` contributes to `binom(L-m+d, d)` strings (`sec2_card_outStr_of_leaf`). Figure
  6 shows these numbers for `L = 6` and `m = 2` (`figure_6`).
* Equation (5): the quotient `β_d / β_{d-1}` comes from the recurrence of the binomial coefficients
  (`Equation5.ratio_nat`, `eq_5_ratio`); for `L = 19m` it is less than `1/2` (`eq_5_bound`); so
  `β_d ≤ 2^{-d} M` by induction on `d` (`eq_5`).
-/

public section

open Finset

namespace ThreeSumApsp

/-! ### One level: which terms contribute to which variables -/












/-- Among the terms contributing to `z`, the number of those equal to `P₀`: one if `z = z₀`, none if
`z = z_ij`. -/
private theorem card_contributing_P0 (z : OutVar) :
    ((univ.filter fun lam : Term => lam.Contributes z).filter fun lam => lam = Term.P0).card
      = if z.IsInner then 1 else 0 := by
  decide +revert

/-- Among the terms contributing to `z`, the number of those different from `P₀`: nine if `z = z₀`,
one if `z = z_ij`. -/
private theorem card_contributing_ne_P0 (z : OutVar) :
    ((univ.filter fun lam : Term => lam.Contributes z).filter fun lam => ¬ lam = Term.P0).card
      = if z.IsInner then 9 else 1 := by
  decide +revert


















/-! ### The order of a leaf -/






/-- Membership in the inner set of an output string. -/
@[simp]
theorem mem_innerSetO {L : ℕ} {η : OutStr L} {ℓ : Fin L} : ℓ ∈ innerSetO η ↔ (η ℓ).IsInner := by
  simp [innerSetO]



















/-- In the proof of Lemma 11: "every leaf of Leaves(U) has an order 0 ≤ d ≤ m".  The upper
bound holds for every leaf. -/
theorem order_le {L : ℕ} (m : ℕ) (τ : Leaf L) : order m τ ≤ m := by
  unfold order
  omega

/-- A leaf has order `d` exactly if it chooses `P₀` at `m - d` levels. -/
theorem order_eq_iff {L : ℕ} (m d : ℕ) (τ : Leaf L) :
    order m τ = d ↔ (P0Levels τ).card + d = m := by
  unfold order
  omega

/-! ### The counts -/










/-- Section 2.4.3: "exactly α_d := binom(m, d) 9^d leaves of order d contribute to an output
string".  As everywhere in Section 2.4.3, the output strings are those whose inner sets have exactly
m elements. -/
theorem sec2_card_contributing_of_order_sourceProof {L m : ℕ} (w : OutStr L) (hw : (innerSetO w).card = m)
    (d : ℕ) :
    (univ.filter fun τ : Leaf L => Leaf.Contributes τ w ∧ order m τ = d).card = alpha m d := by
  by_cases hd : d ≤ m
  · -- Sort the strings of terms that contribute to `w` level by level and have `P₀` at exactly
    -- `m - d` levels by the set `S` of these levels.
    have hcount := Finset.card_pi_places_card
      (fun ℓ => univ.filter fun lam : Term => lam.Contributes (w ℓ)) (fun lam => lam = Term.P0)
      (m - d)
    simp only [card_contributing_P0, card_contributing_ne_P0] at hcount
    -- Given `S`, there is no such string unless `S ⊆ Q`.  Then there are nine choices at each of
    -- the `|Q| - |S| = d` levels of `Q` outside `S`, and one choice at every other level.
    have hgiven : ∀ S ∈ powersetCard (m - d) (univ : Finset (Fin L)),
        (∏ ℓ, if ℓ ∈ S then (if (w ℓ).IsInner then 1 else 0) else (if (w ℓ).IsInner then 9 else 1))
          = if S ⊆ innerSetO w then 9 ^ d else 0 := by
      intro S hS
      have hQS := prod_ite_ite_subset (innerSetO w) S 9
      rw [hw, (mem_powersetCard.mp hS).2, Nat.sub_sub_self hd] at hQS
      rw [← hQS]
      exact prod_congr rfl fun ℓ _ => by simp
    -- There are `binom(m, m - d) = binom(m, d)` sets `S ⊆ Q`.
    rw [sum_congr rfl hgiven, sum_powersetCard_ite_subset, hw, Nat.choose_symm hd] at hcount
    -- These strings are the leaves of order `d` that contribute to `w`.
    rw [alpha, ← hcount]
    refine congrArg card (Finset.ext fun τ => ?_)
    simp only [mem_filter, mem_univ, true_and, order_eq_iff]
    exact and_congr Iff.rfl (by unfold P0Levels; omega)
  · -- No leaf has order more than `m`.
    rw [alpha, Nat.choose_eq_zero_of_lt (by omega), zero_mul, card_eq_zero]
    refine filter_eq_empty_iff.mpr fun τ _ h => ?_
    have hle := order_le m τ
    omega














































































































































end ThreeSumApsp

end


theorem solution : ∀ {L m : Nat} (w : ThreeSumApsp.OutStr L),
  @Eq.{1} Nat (@Finset.card.{0} (Fin L) (@ThreeSumApsp.innerSetO L w)) m →
    ∀ (d : Nat),
      @Eq.{1} Nat
        (@Finset.card.{0} (ThreeSumApsp.Leaf L)
          {τ : ThreeSumApsp.Leaf L |
            And (@ThreeSumApsp.Leaf.Contributes L τ w)
              (@Eq.{1} Int (@ThreeSumApsp.order L m τ) (@Nat.cast.{0} Int instNatCastInt d))})
        (ThreeSumApsp.alpha m d) := by
  exact @ThreeSumApsp.sec2_card_contributing_of_order_sourceProof

#print axioms solution
