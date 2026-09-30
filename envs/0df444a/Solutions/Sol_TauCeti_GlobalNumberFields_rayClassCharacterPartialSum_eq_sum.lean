-- Prove2me | solution 1 for TauCeti.GlobalNumberFields.rayClassCharacterPartialSum_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:16:55.558362+00:00
-- url     : https://prove2.me/submissions/71ac6e0a-35d6-4e9f-b5a1-839b7684968b

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Basic
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Character_Basic
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Character_Sum
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Count_Basic
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Modulus
import Definitions.Def_TauCeti_NumberTheory_NumberField_Ideal_Away
import Definitions.Def_TauCeti_Order_Northcott_Basic
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Factorization
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Ideal
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Algebra.Order.Ring.Units
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Data.Int.WithZero
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Card
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Group
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.UniformSpace.Real

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Finite real-cutoff carriers for Northcott functions

This file packages the finite carrier selected by a real cutoff for a natural-valued Northcott
function, together with generic summatory functions over that carrier. The carrier depends only
on the integer part of the cutoff, and for a nonnegative cutoff it agrees with the one selected by
its natural floor.
-/

 section

namespace TauCeti

open Filter
open scoped Topology

variable {ι : Type*} (N : ι → ℕ) [Northcott N]





/-- An index belongs to `normLE N x` exactly when its `N`-value is at most the inclusive
real cutoff `x`. -/
@[simp, grind =]
theorem mem_normLE {i : ι} {x : ℝ} : i ∈ normLE N x ↔ (N i : ℝ) ≤ x := by
  simp [normLE]

@[simp]
theorem coe_normLE (x : ℝ) : (normLE N x : Set ι) = {i : ι | (N i : ℝ) ≤ x} := by
  ext i
  simp















/-! ### Generic summatory functions -/



/-- Evaluating `summatory N w` at `x` gives the finite sum of `w` over `normLE N x`. -/
theorem summatory_apply {M : Type*} [AddCommMonoid M] (w : ι → M) (x : ℝ) :
    summatory N w x = ∑ i ∈ normLE N x, w i := by
  rw [summatory]





























end TauCeti

end
end

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Ray class characters

A ray class character of a modulus `𝔪` is a multiplicative character of its finite ray class
group with values in the complex units.  Composing with `idealClass 𝔪` evaluates it on the
nonzero integral ideals prime to the finite part of `𝔪`; the coprimality proof remains in the
domain because `idealClass 𝔪` is defined only on those ideals.

When `𝔪 ∣ 𝔫`, pullback along the surjective transition `classMap : Cl_𝔫 → Cl_𝔪` induces a
character of the larger modulus.  These pullbacks are injective, compose along chains of moduli,
and agree with the inclusion of integral ideals prime to the larger modulus.  This is the finite
character API used in ray-class counting and in the factorization of cyclotomic Galois
characters.

## Main definitions

* `TauCeti.GlobalNumberFields.RayClassCharacter`: multiplicative complex-unit characters of a
  ray class group;
* `TauCeti.GlobalNumberFields.RayClassCharacter.onIdeals`: evaluation on integral ideals prime
  to the modulus;
* `TauCeti.GlobalNumberFields.RayClassCharacter.induced`: pullback of a character along a change
  of modulus.

## Main results

* `TauCeti.GlobalNumberFields.RayClassCharacter.ext`: a ray class character is
  determined by its values on integral ideals;
* `TauCeti.GlobalNumberFields.RayClassCharacter.induced_injective`: increasing the modulus does
  not identify distinct characters;
* `TauCeti.GlobalNumberFields.RayClassCharacter.onIdeals_induced`: change of modulus commutes
  with evaluation on ideals.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
* S. Lang, *Algebraic Number Theory*, Chapter VII, §1.
-/

 section

open scoped _root_.NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]



namespace RayClassCharacter

variable {𝔪 𝔫 𝔬 : Modulus K}



/-- Evaluating a ray class character on an ideal is evaluation at the ideal's ray class. -/
@[simp]
theorem onIdeals_apply (χ : RayClassCharacter 𝔪) (I : integralIdealsPrimeTo 𝔪) :
    χ.onIdeals I = χ (idealClass 𝔪 I) :=
  by simp [onIdeals]

















end RayClassCharacter

end TauCeti.GlobalNumberFields

end
end

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Counting the integral ideals of a ray class

Let `𝔪` be a modulus of a number field `K` and `c` a ray class of `𝔪`.  This file introduces
`rayClassIdealCountingFunction 𝔪 c x`, the number of nonzero integral ideals prime to the finite
part of `𝔪` that lie in the class `c` and have norm at most `x`, and proves the two facts that
make it a counting function at all: the sets being counted are finite, and summing over the ray
class group recovers the unrestricted count.

The carrier is `integralIdealsPrimeTo 𝔪`, the monoid on which `idealClass` is defined, so
coprimality and nonvanishing are forced by the type rather than imposed as side conditions; the
zero ideal and ideals sharing a prime with the finite part cannot enter the count.

Finiteness is not proved here. `TauCeti.Order.Northcott.Basic` already fixes the project's
convention
for counting by an *inclusive real* cutoff, and supplies `finite_setOf_natCast_le` for any
natural-valued Northcott function.  All this file adds is the `Northcott` instance for the absolute
norm on `integralIdealsPrimeTo 𝔪`; the finiteness, and with it `normLE`, `summatory` and
`Nat.card_coe_normLE`, then come from that shared layer.  The bound is taken in `ℝ` rather than `ℕ`
because the asymptotics that consume this count are.

The partition is stated first as an equivalence, `idealClassSigmaEquiv`, and only then in counting
form.  The equivalence needs no finiteness at all, and it is what a consumer weighting the classes
by a character reaches for; the counting statement is its `Nat.card` shadow.

## Main definitions

* `TauCeti.GlobalNumberFields.rayClassIdealCountingFunction`: the number of nonzero integral ideals
  prime to `𝔪` in a fixed ray class with norm at most `x`.
* `TauCeti.GlobalNumberFields.idealClassSigmaEquiv`: the ideals prime to `𝔪` of norm at most `x`,
  partitioned into their ray classes.

## Main results

* `TauCeti.GlobalNumberFields.sum_rayClassIdealCountingFunction`: the class counts sum to the
  unrestricted count of nonzero integral ideals prime to `𝔪` of norm at most `x`.
* `TauCeti.GlobalNumberFields.rayClassIdealCountingFunction_def`,
  `TauCeti.GlobalNumberFields.idealClassSigmaEquiv_apply_coe` and
  `TauCeti.GlobalNumberFields.idealClassSigmaEquiv_symm_apply_fst`: the characteristic lemmas of
  the two definitions, so that a consumer never has to unfold either.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
* `CBirkbeck/AINTLIB` @ `2622c61d2502159c62865a1b59fc1de473519113` (Apache-2.0, Chris Birkbeck),
  `projects/Chebotarev/CebotarevDensity/ForMathlib/IdealCongruenceCount.lean`:
  `card_norm_le_residue_eq_sum_class` is the corresponding partition step, stated there for the
  ordinary class group together with a norm-residue condition.
-/

 section

open IsDedekindDomain NumberField
open scoped nonZeroDivisors NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-! ### Finiteness of the sets being counted -/







/-! ### The counting function and the class partition -/



/-- **The counting function as the cardinality defining it.**  The rewrite rule turning
`rayClassIdealCountingFunction` into the set of ideals of class `c` whose norm is at most `x`. -/
theorem rayClassIdealCountingFunction_def (𝔪 : Modulus K) (c : RayClassGroup 𝔪) (x : ℝ) :
    rayClassIdealCountingFunction 𝔪 c x =
      Nat.card {I : integralIdealsPrimeTo 𝔪 //
        idealClass 𝔪 I = c ∧ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x} :=
  (rfl)



/-- The partition keeps the ideal: it only forgets which class the ideal was filed under. -/
@[simp]
theorem idealClassSigmaEquiv_apply_coe (𝔪 : Modulus K) (x : ℝ)
    (p : Σ c : RayClassGroup 𝔪, {I : integralIdealsPrimeTo 𝔪 //
      idealClass 𝔪 I = c ∧ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x}) :
    (idealClassSigmaEquiv 𝔪 x p : integralIdealsPrimeTo 𝔪) = p.2 :=
  (rfl)





end TauCeti.GlobalNumberFields

end
end

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Character sums over the integral ideals of bounded norm

Let `𝔪` be a modulus of a number field `K` and `χ` a ray class character of `𝔪`.  This file
introduces `rayClassCharacterPartialSum 𝔪 χ x`, the sum of `χ` over the nonzero integral ideals
prime to the finite part of `𝔪` whose norm is at most `x`, and identifies it with the
`χ`-weighted combination of the ray class counting functions.

The sum ranges over ideals, not over chosen class representatives.  Regrouping it by ray class is
exactly the partition `idealClassSigmaEquiv`, and on each fibre `χ` is constant, so each class
contributes its counting function scaled by the single value `χ` takes there.

## Main definitions

* `TauCeti.GlobalNumberFields.rayClassCharacterPartialSum`: the partial sum of a ray class
  character over the integral ideals of bounded norm.

## Main results

* `TauCeti.GlobalNumberFields.rayClassCharacterPartialSum_eq_sum`: the partial sum is
  `∑ c, χ c * rayClassIdealCountingFunction 𝔪 c x`.
-/

 section

namespace TauCeti.GlobalNumberFields
end TauCeti.GlobalNumberFields
section TauCeti.GlobalNumberFields
open TauCeti TauCeti.GlobalNumberFields

open scoped _root_.NumberField

variable {K : Type*} [Field K] [NumberField K]



open scoped Classical in
/-- **The partial sum as the `finsum` defining it.**  The rewrite rule turning
`rayClassCharacterPartialSum` into the sum of `χ.onIdeals` over the integral ideals prime to `𝔪`
of norm at most `x`. -/
theorem TauCeti.GlobalNumberFields.rayClassCharacterPartialSum_def (𝔪 : _root_.TauCeti.GlobalNumberFields.Modulus K) (χ : _root_.TauCeti.GlobalNumberFields.RayClassCharacter 𝔪) (x : ℝ) :
    _root_.TauCeti.GlobalNumberFields.rayClassCharacterPartialSum 𝔪 χ x =
      ∑ᶠ I : {I : _root_.TauCeti.GlobalNumberFields.integralIdealsPrimeTo 𝔪 // (_root_.Ideal.absNorm (I : _root_.Ideal (𝓞 K)) : ℝ) ≤ x},
        (χ.onIdeals (I : _root_.TauCeti.GlobalNumberFields.integralIdealsPrimeTo 𝔪) : ℂ) := by
  rw [_root_.TauCeti.GlobalNumberFields.rayClassCharacterPartialSum, _root_.TauCeti.summatory_apply, ← _root_.finsum_mem_coe_finset, _root_.TauCeti.coe_normLE]
  exact (_root_.finsum_set_coe_eq_finsum_mem _).symm

/-- **A character partial sum is the weighted combination of the class counts.**  The partial sum
of `χ` over the integral ideals prime to `𝔪` of norm at most `x` is the sum of the ray class
counting functions, each weighted by the value `χ` takes on its class. -/
theorem solution (𝔪 : _root_.TauCeti.GlobalNumberFields.Modulus K) [_root_.Fintype (_root_.TauCeti.GlobalNumberFields.RayClassGroup 𝔪)]
    (χ : _root_.TauCeti.GlobalNumberFields.RayClassCharacter 𝔪) (x : ℝ) :
    _root_.TauCeti.GlobalNumberFields.rayClassCharacterPartialSum 𝔪 χ x =
      ∑ c : _root_.TauCeti.GlobalNumberFields.RayClassGroup 𝔪, (χ c : ℂ) * _root_.TauCeti.GlobalNumberFields.rayClassIdealCountingFunction 𝔪 c x := by
  have : _root_.Fintype {I : _root_.TauCeti.GlobalNumberFields.integralIdealsPrimeTo 𝔪 //
      (_root_.Ideal.absNorm (I : _root_.Ideal (𝓞 K)) : ℝ) ≤ x} := _root_.Fintype.ofFinite _
  have (c : _root_.TauCeti.GlobalNumberFields.RayClassGroup 𝔪) : _root_.Fintype {I : _root_.TauCeti.GlobalNumberFields.integralIdealsPrimeTo 𝔪 //
      _root_.TauCeti.GlobalNumberFields.idealClass 𝔪 I = c ∧ (_root_.Ideal.absNorm (I : _root_.Ideal (𝓞 K)) : ℝ) ≤ x} := _root_.Fintype.ofFinite _
  -- regroup the ideals of norm at most `x` by ray class
  rw [_root_.TauCeti.GlobalNumberFields.rayClassCharacterPartialSum_def, _root_.finsum_eq_sum_of_fintype,
    ← _root_.Equiv.sum_comp (_root_.TauCeti.GlobalNumberFields.idealClassSigmaEquiv 𝔪 x), _root_.Fintype.sum_sigma]
  refine _root_.Finset.sum_congr _root_.rfl fun c _ ↦ ?_
  -- on the fibre over `c` the character is constantly `χ c`, so the block is a multiple of it
  simp only [_root_.TauCeti.GlobalNumberFields.RayClassCharacter.onIdeals_apply, _root_.TauCeti.GlobalNumberFields.idealClassSigmaEquiv_apply_coe]
  rw [_root_.Finset.sum_eq_card_nsmul fun p _ ↦ by rw [p.2.1]]
  simp [_root_.TauCeti.GlobalNumberFields.rayClassIdealCountingFunction_def, _root_.mul_comm]

end TauCeti.GlobalNumberFields

end
end
