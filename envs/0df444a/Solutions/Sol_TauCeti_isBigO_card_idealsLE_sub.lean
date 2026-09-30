-- Prove2me | solution 1 for TauCeti.isBigO_card_idealsLE_sub
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:58:19.361795+00:00
-- url     : https://prove2.me/submissions/8eb35dfa-85b7-44ab-89c6-158e1d6e5b4f

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_Algebra_Order_Ring_Units
import Definitions.Def_TauCeti_GroupTheory_Index_Basic
import Definitions.Def_TauCeti_LinearAlgebra_Pi
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Counting
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Definitions.Def_TauCeti_NumberTheory_NumberField_CanonicalEmbedding_MulVolume
import Definitions.Def_TauCeti_NumberTheory_NumberField_CanonicalEmbedding_UnitAction
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_Approximation_Weak
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_Counting_CongruenceLattice
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_Counting_RayFundamentalDomain_Basic
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_Counting_RayFundamentalDomain_IntegerSet
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_Counting_Ray_Ideal_Count
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_Counting_Ray_Ideal_Set
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Basic
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_CongruenceQuotient
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Count_Basic
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Exact
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Finite
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Integral
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_MainTerm
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Modulus
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Residue
import Definitions.Def_TauCeti_NumberTheory_NumberField_Ideal_Away
import Definitions.Def_TauCeti_NumberTheory_NumberField_SignApproximation
import Definitions.Def_TauCeti_NumberTheory_NumberField_TotallyPositive
import Definitions.Def_TauCeti_NumberTheory_NumberField_Units_Signature_Basic
import Definitions.Def_TauCeti_NumberTheory_NumberField_Units_Signature_Integer
import Definitions.Def_TauCeti_Order_Northcott_Basic
import Definitions.Def_TauCeti_RingTheory_ClassGroup_Basic
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Factorization
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Ideal
import Definitions.Def_TauCeti_RingTheory_Ideal_Quotient_Representative
import Definitions.Def_TauCeti_RingTheory_NormTrace_Pi
import Definitions.Def_TauCeti_RingTheory_NormTrace_Prod
import Definitions.Def_TauCeti_RingTheory_Valuation_AbsoluteValue
import Definitions.Def_TauCeti_RingTheory_Valuation_Approximation
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Algebra.Order.Ring.Units
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Int.WithZero
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.FractionalIdeal
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.UniformSpace.Real
import Theorems.Thm_Ideal_card_units_quotient_pow_mul_absNorm
import Theorems.Thm_Ideal_isCoprime_iff_exists_mem_and_sub_one_mem
import Theorems.Thm_Ideal_setOf_mem_and_sub_one_mem_eq_vadd_inf
import Theorems.Thm_TauCeti_GlobalNumberFields_classMap_surjective
import Theorems.Thm_TauCeti_GlobalNumberFields_exists_abs_ncard_rayFundamentalDomain_inter_norm_le_inter_vadd_sub_le
import Theorems.Thm_TauCeti_GlobalNumberFields_idealClass_surjective
import Theorems.Thm_TauCeti_GlobalNumberFields_index_unitsCongruenceSubgroup_mul_card_unitsCongruenceTorsion
import Theorems.Thm_TauCeti_GlobalNumberFields_ker_residueSignRayClass
import Theorems.Thm_TauCeti_GlobalNumberFields_oneEquivClassGroup_rayClassMk
import Theorems.Thm_TauCeti_GlobalNumberFields_unitsCongruenceSubgroup_smul_mem_rayFundamentalDomain_iff_mem_torsion
import Theorems.Thm_TauCeti_NumberField_mixedEmbedding_volume_eq_two_pow_mul_volume_inter_pos

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Evaluating the first isomorphism theorem on a class

Mathlib packages the first isomorphism theorem for a surjective homomorphism `φ : G →* M` as
`QuotientGroup.quotientKerEquivOfSurjective φ hφ : G ⧸ φ.ker ≃* M`. It is defined through
`QuotientGroup.quotientKerEquivOfRightInverse` applied to a right inverse extracted from `hφ`
by choice, so evaluating it on a class otherwise means unfolding that noncomputable
implementation.

This file records the computation rule on classes, so that users never have to. It is the
group-theoretic counterpart of Mathlib's `RingHom.quotientKerEquivOfSurjective_apply_mk`, and
belongs beside `QuotientGroup.quotientKerEquivOfSurjective` in Mathlib.

## Main statements

* `TauCeti.QuotientGroup.quotientKerEquivOfSurjective_apply_mk`: the isomorphism
  `G ⧸ φ.ker ≃* M` sends the class of `g` to `φ g`; its additive counterpart is
  `TauCeti.QuotientAddGroup.quotientKerEquivOfSurjective_apply_mk`.
-/

 section

namespace TauCeti

namespace QuotientGroup

variable {G M : Type*} [Group G] [Group M] (φ : G →* M) (hφ : Function.Surjective φ)

/-- The first isomorphism theorem for a surjective homomorphism sends the class of `g` to
`φ g`. -/
@[to_additive (attr := simp) TauCeti.QuotientAddGroup.quotientKerEquivOfSurjective_apply_mk
  /-- The first isomorphism theorem for a surjective additive homomorphism sends the class of
  `g` to `φ g`. -/]
theorem quotientKerEquivOfSurjective_apply_mk (g : G) :
    _root_.QuotientGroup.quotientKerEquivOfSurjective φ hφ (_root_.QuotientGroup.mk g) = φ g :=
  rfl

end QuotientGroup

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

















/-! ### Generic summatory functions -/

































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
# The ray class group of a modulus

Let `𝔪` be a modulus of a number field `K`.  The **ray** of `𝔪` is the subgroup of principal
fractional ideals generated by the elements of `Kˣ` congruent to one modulo `𝔪`, and the **ray
class group** `RayClassGroup 𝔪` is the quotient of the group `idealsPrimeTo 𝔪` of invertible
fractional ideals prime to the finite part of `𝔪` by that ray.

The ray really is a subgroup of `idealsPrimeTo 𝔪`, and not merely of all invertible fractional
ideals: an element congruent to one is a unit at every prime dividing the finite part of `𝔪`
(`IsCongrOne.valuation_eq_one`), so its principal ideal has vanishing multiplicity there.  That is
the content of `TauCeti.GlobalNumberFields.rayHom`, from which the ray is obtained as a range.

The class of an ideal is defined on the monoid `integralIdealsPrimeTo 𝔪` of nonzero integral ideals
prime to the finite part, never on all of `Ideal (𝓞 K)`: an ideal sharing a prime with the finite
part has no ray class, and carrying the coprimality proof in the argument makes multiplicativity
literally `map_mul`.

For the trivial modulus the congruence condition is empty, and the ray class group is the ordinary
class group (`oneEquivClassGroup`).

## Main definitions

* `TauCeti.GlobalNumberFields.principalIdealPrimeTo`: the principal fractional ideals whose
  generators are units at the finite part.
* `TauCeti.GlobalNumberFields.rayHom`, `TauCeti.GlobalNumberFields.ray`: the principal ideals of
  the elements congruent to one, and the subgroup they form.
* `TauCeti.GlobalNumberFields.idealsPrimeToClassGroup`: the ordinary ideal class of an invertible
  fractional ideal prime to a modulus.
* `TauCeti.GlobalNumberFields.RayClassGroup`: the quotient of `idealsPrimeTo 𝔪` by the ray, with
  `TauCeti.GlobalNumberFields.rayClassMk` and the universal property
  `TauCeti.GlobalNumberFields.rayClassLift`.
* `TauCeti.GlobalNumberFields.idealClass`: the ray class of an integral ideal prime to `𝔪`, as a
  monoid homomorphism out of `integralIdealsPrimeTo 𝔪`.
* `TauCeti.GlobalNumberFields.classMap`: the transition map, running from the ray class group of a
  larger modulus to that of a divisor of it.

## Main results

* `TauCeti.GlobalNumberFields.toPrincipalIdeal_mem_idealsPrimeTo_iff`: a principal fractional ideal
  is prime to the modulus exactly when its generator is a unit at every prime dividing the finite
  part, with `TauCeti.GlobalNumberFields.IsCongrOne.toPrincipalIdeal_mem_idealsPrimeTo` the
  consequence for an element congruent to one.
* `TauCeti.GlobalNumberFields.idealsPrimeTo_eq_top`: every invertible fractional ideal is prime
  to a modulus whose support is empty, so `TauCeti.GlobalNumberFields.idealsPrimeToEquiv`
  identifies the two carriers there.
* `TauCeti.GlobalNumberFields.idealClass_apply`: the ray class of an integral ideal is the ray
  class of the fractional ideal it generates.
* `TauCeti.GlobalNumberFields.idealClass_mul`: taking the ray class of an integral ideal respects
  multiplication.
* `TauCeti.GlobalNumberFields.idealClass_eq_one_iff`: an ideal has trivial ray class exactly when
  it is generated, as a fractional ideal, by an element of `Kˣ` congruent to one modulo `𝔪`.
* `TauCeti.GlobalNumberFields.classMap_comp_classMap` and
  `TauCeti.GlobalNumberFields.classMap_comp_idealClass`: the transition maps compose along a tower
  of moduli, and carry the class of an integral ideal to the class of the same ideal.  Both are
  equalities of homomorphisms, with the pointwise forms `classMap_classMap` and
  `classMap_idealClass` derived from them.  The transition map from a modulus to itself is the
  identity (`TauCeti.GlobalNumberFields.classMap_refl`).
* `TauCeti.GlobalNumberFields.oneEquivClassGroup`: at the trivial modulus the ray class group is
  the class group of `𝓞 K`, carrying a ray class to the class of the same fractional ideal
  (`TauCeti.GlobalNumberFields.oneEquivClassGroup_rayClassMk`).

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
* S. Lang, *Algebraic Number Theory*, Chapter VI, §1.
-/

 section

open _root_.IsDedekindDomain _root_.IsDedekindDomain.HeightOneSpectrum _root_.NumberField
open scoped _root_.nonZeroDivisors _root_.NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]





































@[simp] theorem rayClassLift_rayClassMk {M : Type*} [Monoid M] {𝔪 : Modulus K}
    (φ : idealsPrimeTo 𝔪 →* M) (h : ray 𝔪 ≤ φ.ker) (I : idealsPrimeTo 𝔪) :
    rayClassLift φ h (rayClassMk 𝔪 I) = φ I := (rfl)



/-- The kernel of `rayClassLift φ h` is the image under `rayClassMk 𝔪` of `φ.ker`.  This exposes
`QuotientGroup.ker_lift` through the module-opaque `RayClassGroup` representation. -/
theorem ker_rayClassLift {M : Type*} [Group M] {𝔪 : Modulus K}
    (φ : idealsPrimeTo 𝔪 →* M) (h : ray 𝔪 ≤ φ.ker) :
    (rayClassLift φ h).ker = Subgroup.map (rayClassMk 𝔪) φ.ker :=
  QuotientGroup.ker_lift (ray 𝔪) φ h









/-! ### The transition map between ray class groups -/



@[simp] theorem classMap_rayClassMk {𝔪 𝔫 : Modulus K} (h : 𝔪 ∣ 𝔫) (I : idealsPrimeTo 𝔫) :
    classMap h (rayClassMk 𝔫 I) =
      rayClassMk 𝔪 (NumberFieldArithmetic.idealsAwayInclusion (Modulus.support_mono h) I) := (rfl)













/-! ### Moduli with unit finite part -/









/-! ### The trivial modulus -/







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
# The residue-and-sign presentation of the congruence quotient

Let `𝔪` be a modulus of a number field `K`.  Congruence to one modulo `𝔪` is two independent
conditions on an element of `primeToSubgroup 𝔪`: reduction to one in `(𝓞 K ⧸ 𝔪.finitePart)ˣ`, and
positivity at each real place selected by `𝔪.infinitePart`.  This file packages the two conditions
into one homomorphism

```text
residueSignHom 𝔪 :
  primeToSubgroup 𝔪 →* (𝓞 K ⧸ 𝔪.finitePart)ˣ × (𝔪.infinitePart → ℤˣ)
```

and proves that it is surjective with kernel exactly `congruenceSubgroup 𝔪`.  The resulting
isomorphism `residueSignEquiv` computes the relative index

```text
(congruenceSubgroup 𝔪).relIndex (primeToSubgroup 𝔪)
  = Nat.card (𝓞 K ⧸ 𝔪.finitePart)ˣ * 2 ^ 𝔪.infinitePart.card,
```

which is the residue-and-sign factor of the ray class number formula — the factor *before* the
image of the global units is divided out — and strengthens the bare finiteness recorded by
`congruenceSubgroup_finiteIndex`.

Surjectivity is the arithmetic content and is *not* a chinese-remainder statement: the residue
class and the signs have to be realized by one and the same element of `Kˣ`, so the proof runs
through weak approximation at the mixed set of places consisting of the primes dividing
`𝔪.finitePart` together with all real places
(`exists_fieldUnit_valuation_sub_lt_and_signHom_eq`).  An approximation to a chosen integral
representative of the residue class, closely enough that `v.valuation K` of their difference stays
below `exp (-𝔪.exponent v)` at each prime of the support, has the same reduction as that
representative: the quotient of the two then differs from one by at most that much, which is the
congruence condition recorded by `residue_eq_one_iff`.

The global units of `K` are nowhere quotiented out here.  Their image in this quotient is the
obstruction that glues the residue-unit and sign factors to the ordinary class group inside the
ray class group, and it is why the ray class group is not the product of the three.

## Main definitions

* `TauCeti.GlobalNumberFields.residueSignHom`: the reduction-and-signs homomorphism.
* `TauCeti.GlobalNumberFields.residueSignEquiv`: the induced isomorphism from the congruence
  quotient.

## Main results

* `TauCeti.GlobalNumberFields.residueSignHom_eq_one_iff` and
  `TauCeti.GlobalNumberFields.ker_residueSignHom`: the kernel is the congruence subgroup.
* `TauCeti.GlobalNumberFields.residueSignHom_surjective`: every residue unit and sign pattern is
  realized simultaneously, together with its archimedean half
  `TauCeti.GlobalNumberFields.modulusSignHom_comp_primeToSubgroup_surjective`.
* `TauCeti.GlobalNumberFields.relIndex_congruenceSubgroup`: the exact relative index.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
* S. Lang, *Algebraic Number Theory*, Chapter VI, §1.
-/

 section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped nonZeroDivisors NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-! ### The signs prescribed by a modulus -/







/-! ### The reduction-and-signs homomorphism -/











/-! ### Surjectivity -/





/-! ### The congruence quotient and its order -/



@[simp] theorem residueSignEquiv_apply_mk (𝔪 : Modulus K) (x : primeToSubgroup 𝔪) :
    residueSignEquiv 𝔪 (QuotientGroup.mk x) = residueSignHom 𝔪 x := by
  simp only [residueSignEquiv, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk,
    TauCeti.QuotientGroup.quotientKerEquivOfSurjective_apply_mk]

/-- **The exact relative index of the congruence subgroup.**  The elements that are units at the
finite part of `𝔪`, modulo those congruent to one, are counted by the residue units modulo the
finite part times two for each real place of the infinite part.

This refines the finiteness statement `congruenceSubgroup_finiteIndex` to an equality.  It is the
residue-and-sign factor entering the ray class number formula, which multiplies the class number
only after the image of the global units in this quotient is divided out; that image is the
obstruction described in the module docstring. -/
theorem relIndex_congruenceSubgroup (𝔪 : Modulus K) :
    (congruenceSubgroup 𝔪).relIndex (primeToSubgroup 𝔪) =
      Nat.card (𝓞 K ⧸ 𝔪.finitePart)ˣ * 2 ^ 𝔪.infinitePart.card := by
  rw [Subgroup.relIndex, ← ker_residueSignHom, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr (residueSignHom_surjective 𝔪),
    Nat.card_congr Subgroup.topEquiv.toEquiv, Nat.card_prod, Nat.card_pi]
  congr 1
  rw [Finset.prod_const, Nat.card_eq_fintype_card, Fintype.card_units_int, Finset.card_univ,
    Fintype.card_coe]

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
# The ray class exact sequence

For a modulus `m` of a number field `K`, forgetting its congruence and sign conditions sends a ray
class to an ordinary ideal class.  This file constructs the full exact sequence

```text
1 → unitsCongruenceSubgroup m → (𝓞 K)ˣ → A m → RayClassGroup m → ClassGroup (𝓞 K) → 1,
```

where `A m = (𝓞 K ⧸ m.finitePart)ˣ × (m.infinitePart → ℤˣ)` records residues and prescribed
signs.  It also retains the useful coarser exact tail
`primeToSubgroup m → RayClassGroup m → ClassGroup (𝓞 K) → 1`.

In the coarser tail, the first map sends an element of `Kˣ` that is a unit at the finite part to
the ray class of its principal ideal.  The second map is surjective, and its kernel is exactly the
range of the first.  Surjectivity of the transition maps follows by weak approximation, and
surjectivity onto the ordinary class group follows by transition to the trivial modulus.

The kernel of `A m → RayClassGroup m` is the image of the integer units, while the kernel of the
map from integer units to `A m` is `unitsCongruenceSubgroup m`.  The resulting exact sequence is
the input to the ray class number formula.

## Main definitions

* `TauCeti.GlobalNumberFields.principalRayClass`: the ray class of a principal fractional ideal
  whose generator is a unit at the finite part.
* `TauCeti.GlobalNumberFields.rayClassToClassGroup`: the ordinary ideal class underlying a ray
  class.
* `TauCeti.GlobalNumberFields.unitsResidueSignHom`: the residues and signs of the integer units.
* `TauCeti.GlobalNumberFields.residueSignRayClass`: the principal ray class of a residue unit and
  sign pattern.

## Main results

* `TauCeti.GlobalNumberFields.rayClassToClassGroup_surjective`: every ordinary ideal class lifts
  to a ray class.
* `TauCeti.GlobalNumberFields.ker_rayClassToClassGroup`: the kernel consists exactly of ray
  classes of principal ideals generated by elements in `primeToSubgroup m`.
* `TauCeti.GlobalNumberFields.mulExact_principalRayClass_rayClassToClassGroup`: the corresponding
  multiplicative exactness statement.
* `TauCeti.GlobalNumberFields.classMap_surjective`: every transition between ray class groups is
  surjective.
* `TauCeti.GlobalNumberFields.ker_unitsResidueSignHom`,
  `TauCeti.GlobalNumberFields.ker_residueSignRayClass` and
  `TauCeti.GlobalNumberFields.range_residueSignRayClass`: the three nontrivial exactness statements
  in the full sequence.
* `TauCeti.GlobalNumberFields.mulExact_unitsCongruenceSubgroup_unitsResidueSignHom`,
  `TauCeti.GlobalNumberFields.mulExact_unitsResidueSignHom_residueSignRayClass` and
  `TauCeti.GlobalNumberFields.mulExact_residueSignRayClass_rayClassToClassGroup`: their
  multiplicative exactness forms.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
* S. Lang, *Algebraic Number Theory*, Chapter VI, §1.
-/

 section

open IsDedekindDomain NumberField
open scoped nonZeroDivisors NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]









/-- The ordinary class underlying the ray class of a fractional ideal is its usual ideal class. -/
@[simp] theorem rayClassToClassGroup_rayClassMk (m : Modulus K) (I : idealsPrimeTo m) :
    rayClassToClassGroup m (rayClassMk m I) =
      ClassGroup.mk K (I : (FractionalIdeal (RingOfIntegers K)⁰ K)ˣ) := by
  rw [rayClassToClassGroup, rayClassLift_rayClassMk, idealsPrimeToClassGroup_apply]

/-- Forgetting the modulus agrees with transition to the trivial modulus followed by the canonical
identification of its ray class group with the ordinary class group. -/
theorem rayClassToClassGroup_eq_oneEquivClassGroup_comp_classMap (m : Modulus K) :
    rayClassToClassGroup m =
      oneEquivClassGroup.toMonoidHom.comp (classMap (Modulus.one_dvd m)) := by
  refine MonoidHom.ext fun c ↦ ?_
  obtain ⟨I, rfl⟩ := rayClassMk_surjective m c
  rw [rayClassToClassGroup_rayClassMk, MonoidHom.comp_apply, classMap_rayClassMk,
    MulEquiv.coe_toMonoidHom, oneEquivClassGroup_rayClassMk,
    NumberFieldArithmetic.coe_idealsAwayInclusion]



/-- Every ordinary ideal class is represented by a ray class. -/
theorem rayClassToClassGroup_surjective (m : Modulus K) :
    Function.Surjective (rayClassToClassGroup m) := by
  rw [rayClassToClassGroup_eq_oneEquivClassGroup_comp_classMap]
  exact oneEquivClassGroup.surjective.comp (classMap_surjective (Modulus.one_dvd m))

/-- The ray classes with trivial ordinary ideal class are exactly the principal ray classes.  This
is exactness at `RayClassGroup m` in the ray-class exact sequence. -/
theorem ker_rayClassToClassGroup (m : Modulus K) :
    (rayClassToClassGroup m).ker = (principalRayClass m).range := by
  rw [rayClassToClassGroup, ker_rayClassLift, ← range_principalIdealPrimeTo,
    principalRayClass, MonoidHom.range_comp]



/-! ### The residue-and-sign presentation of the exact sequence -/





@[simp] theorem unitsResidueSignHom_apply (𝔪 : Modulus K) (u : (𝓞 K)ˣ) :
    unitsResidueSignHom 𝔪 u = residueSignHom 𝔪 (unitsToPrimeToSubgroup 𝔪 u) := (rfl)

/-- **Exactness at the integer units**: a unit has trivial residue and trivial signs exactly when
it is congruent to one modulo `𝔪`. -/
theorem ker_unitsResidueSignHom (𝔪 : Modulus K) :
    (unitsResidueSignHom 𝔪).ker = unitsCongruenceSubgroup 𝔪 := by
  ext u
  rw [MonoidHom.mem_ker, unitsResidueSignHom_apply, residueSignHom_eq_one_iff,
    coe_unitsToPrimeToSubgroup, mem_unitsCongruenceSubgroup, mem_congruenceSubgroup]





/-- The class attached to the residue and signs of an element is its principal ray class. -/
@[simp] theorem residueSignRayClass_residueSignHom (𝔪 : Modulus K) (x : primeToSubgroup 𝔪) :
    residueSignRayClass 𝔪 (residueSignHom 𝔪 x) = principalRayClass 𝔪 x := by
  rw [residueSignRayClass, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    (residueSignEquiv 𝔪).symm_apply_eq.mpr (residueSignEquiv_apply_mk 𝔪 x).symm,
    QuotientGroup.lift_mk]

/-- `residueSignRayClass 𝔪` is the factorization of `principalRayClass 𝔪` through the surjection
`residueSignHom 𝔪`. -/
theorem residueSignRayClass_comp_residueSignHom (𝔪 : Modulus K) :
    (residueSignRayClass 𝔪).comp (residueSignHom 𝔪) = principalRayClass 𝔪 :=
  MonoidHom.ext (residueSignRayClass_residueSignHom 𝔪)



/-- **Exactness at the ray class group**: the ray classes with trivial ordinary ideal class are
exactly the classes of residue units and sign patterns. -/
theorem range_residueSignRayClass (𝔪 : Modulus K) :
    (residueSignRayClass 𝔪).range = (rayClassToClassGroup 𝔪).ker := by
  rw [ker_rayClassToClassGroup, ← residueSignRayClass_comp_residueSignHom, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (residueSignHom_surjective 𝔪), ← MonoidHom.range_eq_map]





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







/-- **The class counts sum to the total.**  Summing `rayClassIdealCountingFunction` over the ray
class group recovers the number of nonzero integral ideals prime to `𝔪` of norm at most `x`.

The ray class group is always finite (`finite_rayClassGroup`), but it carries no canonical
`Fintype`, so the enumeration is taken as a hypothesis rather than fixed to `Fintype.ofFinite`
here; that keeps the statement usable against whichever enumeration the caller holds. -/
theorem sum_rayClassIdealCountingFunction (𝔪 : Modulus K) [Fintype (RayClassGroup 𝔪)] (x : ℝ) :
    ∑ c : RayClassGroup 𝔪, rayClassIdealCountingFunction 𝔪 c x =
      Nat.card {I : integralIdealsPrimeTo 𝔪 // (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x} :=
  Nat.card_sigma.symm.trans (Nat.card_congr (idealClassSigmaEquiv 𝔪 x))

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
# The main term of the ray class ideal count

This file defines the main term of the ray class ideal count and proves it positive: the number
of integral ideals of a fixed ray class with absolute norm at most `x` is this coefficient times
`x`, up to a power-saving error; this is
`TauCeti.GlobalNumberFields.isBigO_rayClassIdealCountingFunction_sub`.

The coefficient is the Dedekind-zeta residue divided by the order of the ray class group, times
one correction factor `1 - (N 𝔭)⁻¹` for each prime `𝔭` in the support of the modulus.  The Euler
factor of `ζ_K` at `𝔭` is `(1 - N 𝔭 ^ (-s))⁻¹`, so deleting `𝔭` from the Euler product multiplies
`ζ_K s` by its reciprocal `1 - N 𝔭 ^ (-s)`; the factor above is that reciprocal at `s = 1`.  The
intended count runs over the ideals prime to the finite part of the modulus, which is what makes
those corrections the right ones.

## Main definitions

* `TauCeti.GlobalNumberFields.rayClassIdealMainTerm`: the coefficient.

## Main results

* `TauCeti.GlobalNumberFields.rayClassIdealMainTerm_eq`: the coefficient written out.
* `TauCeti.GlobalNumberFields.rayClassIdealMainTerm_one`: at the trivial modulus it is the
  Dedekind-zeta residue over the class number.
* `TauCeti.GlobalNumberFields.rayClassIdealMainTerm_pos`: it is positive.

## References

* S. Lang, *Algebraic Number Theory*, Chapter VIII, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5.
-/

 section

open IsDedekindDomain NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]



/-- **The coefficient, written out.**  The Dedekind-zeta residue divided by the order of the ray
class group, times the correction factors at the primes dividing the finite part of the modulus. -/
theorem rayClassIdealMainTerm_eq (𝔪 : Modulus K) :
    rayClassIdealMainTerm 𝔪 = dedekindZeta_residue K / (Nat.card (RayClassGroup 𝔪) : ℝ) *
      ∏ v ∈ 𝔪.support, (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹) :=
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
# The index of one ideal lattice in another

An invertible fractional ideal `I` of a number field `K` is a full `ℤ`-lattice in `K`, and its
image `mixedEmbedding.idealLattice K I` is a full lattice in the mixed space.  If `J ≤ I` are two
such ideals, the index of `J` in `I` is the ratio of their absolute norms.  This is the
lattice-theoretic meaning of the norm of a fractional ideal: for an integral ideal `𝔞`, the
lattice of `I * 𝔞` has index `N 𝔞` in the lattice of `I`, which is how congruence conditions
modulo `𝔞` are counted among the lattice points of `I`.

The index is computed in `K` by `NumberField.relIndex_fractionalIdeal_eq_absNorm_div_absNorm`, and
transported to the mixed space along the injective embedding.

## Main results

* `NumberField.mixedEmbedding.relIndex_idealLattice`: the index of the lattice of `J` in the
  lattice of `I` is `absNorm J / absNorm I`.
* `NumberField.mixedEmbedding.relIndex_idealLattice_mul_mk0`: the lattice of `I * 𝔞` has index
  `N 𝔞` in the lattice of `I`.
* `NumberField.mixedEmbedding.covolume_idealLattice_mul_mk0`: the covolume of the lattice of
  `I * 𝔞` is `N 𝔞` times the covolume of the lattice of `I`.
-/

 section

open Module NumberField
open scoped nonZeroDivisors

namespace NumberField.mixedEmbedding

variable {K : Type*} [Field K] [NumberField K]







open scoped Classical in
/-- **The covolume of the lattice of `I * 𝔞`** is `N 𝔞` times the covolume of the lattice of
`I`. -/
theorem covolume_idealLattice_mul_mk0 (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (𝔞 : (Ideal (𝓞 K))⁰) :
    ZLattice.covolume (idealLattice K (I * FractionalIdeal.mk0 K 𝔞)) =
      Ideal.absNorm (𝔞 : Ideal (𝓞 K)) * ZLattice.covolume (idealLattice K I) := by
  rw [covolume_idealLattice, covolume_idealLattice, Units.val_mul, map_mul,
    FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm]
  push_cast
  ring

end NumberField.mixedEmbedding

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
# The congruence lattice of a modulus

Let `𝔪` be a modulus of a number field `K` with finite part `𝔪₀`, and let `I` be an invertible
fractional ideal.  Under the mixed embedding `K → ℝ^r₁ × ℂ^r₂`, the ideal `I` becomes the full
lattice `mixedEmbedding.idealLattice K I`.  The **congruence lattice** `congruenceLattice 𝔪 I` is
the sublattice coming from `I * 𝔪₀`: the elements of `I` congruent to `0` modulo `I * 𝔪₀`.

Counting the elements of `I` in a region that satisfy a congruence `x ≡ a mod I * 𝔪₀` is
counting the points of one coset of this sublattice, which is itself a translate of a full
lattice.  The index computation below says that there are exactly `N 𝔪₀` such cosets, and the
covolume grows by the factor `N 𝔪₀`.  These are the lattice inputs to counting integral ideals in
a ray class.

Only the finite part `𝔪₀` enters the lattice: the infinite part of `𝔪` plays no role here, and
the sign conditions at the real places of `𝔪.infinitePart` are imposed by the region, not by the
sublattice.

## Main definitions

* `TauCeti.GlobalNumberFields.congruenceLattice`: the lattice of `I * 𝔪₀` in the mixed space.

## Main results

* `TauCeti.GlobalNumberFields.mem_congruenceLattice_iff`: its points are the images of the
  elements of `I * 𝔪₀`.
* `TauCeti.GlobalNumberFields.coe_congruenceLattice_mk0_eq_image`: for an integral ideal `𝔞`,
  the same description over `𝔞 * 𝔪₀`.
* `TauCeti.GlobalNumberFields.congruenceLattice_le_idealLattice`: it is a sublattice of the ideal
  lattice of `I`.
* `TauCeti.GlobalNumberFields.relIndex_congruenceLattice`: its index in the ideal lattice of `I`
  is the absolute norm of `𝔪₀`.
* `TauCeti.GlobalNumberFields.covolume_congruenceLattice`: its covolume is `N 𝔪₀` times the
  covolume of the ideal lattice of `I`.
* `TauCeti.GlobalNumberFields.covolume_congruenceLattice_div_absNorm`: its covolume divided by
  `N I` is `N 𝔪₀ · √|d_K| / 2 ^ r₂`.
* `TauCeti.GlobalNumberFields.congruenceLattice_eq_of_finitePart_eq`: it depends only on the
  finite part of the modulus.
* `TauCeti.GlobalNumberFields.congruenceLattice_eq_idealLattice_of_finitePart_eq_top`: for a
  modulus with trivial finite part it is the ideal lattice itself; `congruenceLattice_one` and
  `congruenceLattice_narrowModulus` are the cases of the trivial and the narrow modulus.

## References

* S. Lang, *Algebraic Number Theory*, Chapter VI, §3.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
-/

 section

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped nonZeroDivisors

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]



/-- The congruence lattice is the ideal lattice of `I * 𝔪₀`. -/
theorem congruenceLattice_def (𝔪 : Modulus K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    congruenceLattice 𝔪 I = idealLattice K (I * FractionalIdeal.mk0 K
      ⟨𝔪.finitePart, mem_nonZeroDivisors_of_ne_zero 𝔪.finitePart_ne_zero⟩) :=
  (rfl)





/-- The points of the congruence lattice are the images of the elements of `I * 𝔪₀`. -/
@[simp]
theorem mem_congruenceLattice_iff {𝔪 : Modulus K} {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    {x : mixedSpace K} :
    x ∈ congruenceLattice 𝔪 I ↔
      ∃ y ∈ (I : FractionalIdeal (𝓞 K)⁰ K) * 𝔪.finitePart, mixedEmbedding K y = x := by
  rw [congruenceLattice_def, mem_idealLattice]
  simp [← FractionalIdeal.mem_coe, FractionalIdeal.coe_mul]





open scoped Classical in
/-- **The covolume of the congruence lattice** is `N 𝔪₀` times the covolume of the ideal lattice
of `I`. -/
@[simp]
theorem covolume_congruenceLattice (𝔪 : Modulus K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (congruenceLattice 𝔪 I) =
      Ideal.absNorm 𝔪.finitePart * ZLattice.covolume (idealLattice K I) := by
  rw [congruenceLattice_def, covolume_idealLattice_mul_mk0]

open scoped Classical in
/-- **The covolume of the congruence lattice, per unit norm.**  For an invertible fractional
ideal `I`, the covolume of the congruence lattice of `𝔪` at `I`, divided by `N I`, is
`N 𝔪₀ · √|d_K| / 2 ^ r₂`, where `d_K` is the discriminant and `r₂` the number of complex places
of `K`; in particular it does not depend on `I`. -/
theorem covolume_congruenceLattice_div_absNorm (𝔪 : Modulus K)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (congruenceLattice 𝔪 I) volume /
        (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) =
      Ideal.absNorm 𝔪.finitePart * √|(discr K : ℝ)| / 2 ^ nrComplexPlaces K := by
  simp only [covolume_congruenceLattice, covolume_idealLattice, inv_pow]
  field_simp









/-- **The congruence lattice of an integral ideal, upstairs.**  For a nonzero integral ideal `𝔞`,
the congruence lattice of `𝔪` at `mk0 𝔞` is the image under `mixedEmbedding` of the ideal
`𝔞 * 𝔪₀` of `𝓞 K`. -/
@[simp]
theorem coe_congruenceLattice_mk0_eq_image (𝔪 : Modulus K) (𝔞 : (Ideal (𝓞 K))⁰) :
    (congruenceLattice 𝔪 (FractionalIdeal.mk0 K 𝔞) : Set (mixedSpace K)) =
      (fun y : 𝓞 K ↦ mixedEmbedding K (y : K)) ''
        ((𝔞 : Ideal (𝓞 K)) * 𝔪.finitePart : Ideal (𝓞 K)) := by
  ext x
  simp [mem_congruenceLattice_iff, FractionalIdeal.coe_mk0, ← FractionalIdeal.coeIdeal_mul,
    FractionalIdeal.mem_coeIdeal]

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
# The elements of one ideal congruent to one modulo another

For ideals `I` and `J` of a commutative ring, the elements of `I` congruent to `1` modulo `J` form
a coset of `I ⊓ J` inside `I`, translated by any one of them.  Such an element exists exactly when
`I` and `J` are coprime, and coprimality also turns `I ⊓ J` into `I * J`.

This is the shape a counting argument wants: the set is a translate of a fixed subgroup, so it can
be enumerated by translating that subgroup once.

## Main results

* `Ideal.isCoprime_iff_exists_mem_and_sub_one_mem`: the set is nonempty exactly when `I`
  and `J` are coprime;
* `Ideal.setOf_mem_and_sub_one_mem_eq_vadd_inf`: the set is a coset of `I ⊓ J`;
* `Ideal.setOf_mem_and_sub_one_mem_eq_vadd_mul`: the same coset written over `I * J`.
-/

 section

namespace Ideal

section Ring

variable {R : Type*} [Ring R] {I J : Ideal R}



end Ring

section CommRing

variable {R : Type*} [CommRing R] {I J : Ideal R}



open Pointwise in
/-- **The set is a coset of `I * J`.**  The elements of `I` congruent to `1` modulo `J` are a
translate of `I * J` by any one of them. -/
theorem setOf_mem_and_sub_one_mem_eq_vadd_mul {ξ : R} (hξI : ξ ∈ I) (hξJ : ξ - 1 ∈ J) :
    {x : R | x ∈ I ∧ x - 1 ∈ J} = ξ +ᵥ ((I * J : Ideal R) : Set R) := by
  -- the `Ideal R` ascription keeps `*` the ideal product: `open Pointwise` also gives `Set R` one
  rw [mul_eq_inf_of_isCoprime (isCoprime_iff_exists_mem_and_sub_one_mem.mpr ⟨ξ, hξI, hξJ⟩),
    setOf_mem_and_sub_one_mem_eq_vadd_inf hξI hξJ]

end CommRing

end Ideal

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
# Elements of an ideal congruent to one, in the mixed space

For a nonzero integral ideal `𝔞` and a modulus `𝔪` with finite part `𝔪₀`, consider the elements
of `𝔞` that are congruent to one modulo `𝔪₀`.  **Provided there is at least one**, they form a
coset of `𝔞 * 𝔪₀` — the set is empty unless such an element exists, which is why the theorem below
takes a witness `ξ` rather than a hypothesis on `𝔞` alone.  A witness comes from coprimality of
`𝔞` and `𝔪₀`, via `Ideal.isCoprime_iff_exists_mem_and_sub_one_mem`.

This file records what the images of those elements look like in the mixed space: a single
translate of `congruenceLattice 𝔪 (FractionalIdeal.mk0 K 𝔞)`.

The lattice being translated depends only on `𝔪` and `𝔞`, not on the element chosen to name the
translate, so those images are the points of one translate of a fixed lattice.

Nothing here asks that `𝔞` represent a given ray class, nor divides out the congruence roots of
unity acting on the ray fundamental domain; a ray-class ideal count imposes both itself.

## Main results

* `TauCeti.GlobalNumberFields.image_setOf_mem_and_sub_one_mem_eq_vadd_congruenceLattice`:
  those images are a translate of the congruence lattice.
-/

 section

open IsDedekindDomain NumberField NumberField.mixedEmbedding

open scoped Pointwise nonZeroDivisors

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- **The elements congruent to one map onto a coset of the congruence lattice.**  For a nonzero
integral ideal `𝔞` and an element `ξ` of `𝔞` congruent to one modulo `𝔪₀`, the elements of `𝔞`
congruent to one modulo `𝔪₀` map onto the translate of
`congruenceLattice 𝔪 (FractionalIdeal.mk0 K 𝔞)` by the image of `ξ`.

Such a `ξ` is what `Ideal.isCoprime_iff_exists_mem_and_sub_one_mem` extracts from
coprimality of `𝔞` and `𝔪₀`, and the lattice on the right does not involve `ξ`: two such
choices give translates of the same lattice. -/
theorem image_setOf_mem_and_sub_one_mem_eq_vadd_congruenceLattice (𝔪 : Modulus K)
    (𝔞 : (Ideal (𝓞 K))⁰) {ξ : 𝓞 K} (hξ𝔞 : ξ ∈ (𝔞 : Ideal (𝓞 K))) (hξ𝔪 : ξ - 1 ∈ 𝔪.finitePart) :
    (fun y : 𝓞 K ↦ mixedEmbedding K (y : K)) ''
        {α : 𝓞 K | α ∈ (𝔞 : Ideal (𝓞 K)) ∧ α - 1 ∈ 𝔪.finitePart} = mixedEmbedding K (ξ : K) +ᵥ
          (congruenceLattice 𝔪 (FractionalIdeal.mk0 K 𝔞) : Set (mixedSpace K)) := by
  rw [Ideal.setOf_mem_and_sub_one_mem_eq_vadd_mul hξ𝔞 hξ𝔪, coe_congruenceLattice_mk0_eq_image]
  -- `rw` cannot finish here: the map in the statement is the coercion of the composite ring hom
  -- only up to unfolding, and `rw` matches syntactically
  exact Set.image_vadd_distrib ((mixedEmbedding K).comp (algebraMap (𝓞 K) K)) ξ _

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
# Fundamental domains for congruence subgroups of number-field units

A unit congruent to one modulo a modulus `𝔪` is constrained in two ways: it lies in a finite-index
subgroup of `(𝓞 K)ˣ`, and it is positive at every real place selected by the infinite part of `𝔪`.
The set `rayFundamentalDomain 𝔪` built here is cut out by the matching two conditions on the mixed
space: the sign conditions prescribed by `𝔪`, recorded by `posRegion 𝔪`, together with membership
in one of finitely many translates of Mathlib's `NumberField.mixedEmbedding.fundamentalCone`.

The translates are indexed by the cosets of `unitsCongruenceSubgroupSupTorsion 𝔪`, the congruence
units *joined with the roots of unity*, and not by the cosets of the congruence units alone.
Mathlib's cone is stable under the torsion, so translating it by two units differing by a root of
unity gives the same set; only with the larger index group do the translates meet each
congruence-unit orbit the same number of times, independently of the point and of the arbitrary
choice of representatives.

Consequently the domain is fundamental *modulo torsion*, in exactly the sense in which Mathlib's
cone is fundamental for the full unit group. It is measurable and stable under positive real
scalars — negative ones may violate nonempty prescribed sign conditions — every point of
`posRegion 𝔪` of nonzero mixed norm is carried into it by a unit congruent to one modulo `𝔪`, and
a congruence unit carries a point of the domain back into the domain exactly when that unit is a
root of unity. So the domain meets each congruence-unit orbit of nonzero mixed norm inside
`posRegion 𝔪` in one point, modulo the congruence units that are roots of unity. For the trivial
modulus, whose infinite part is empty and whose congruence units are all of `(𝓞 K)ˣ`, the domain
*is* Mathlib's fundamental cone.

Boundary regularity — Lipschitz parametrizability of the frontier of the norm-one section — is
developed separately; it is what upgrades the orbit description below to a count of the algebraic
integers in a fixed ray class.

## Main definitions

* `TauCeti.GlobalNumberFields.unitsCongruenceSubgroupSupTorsion`: the join of the units congruent
  to one modulo `𝔪` with the roots of unity;
* `TauCeti.GlobalNumberFields.posRegion`: the sign conditions prescribed by the infinite part;
* `TauCeti.GlobalNumberFields.rayUnitRepresentative`: a normalized representative of a coset of
  that subgroup;
* `TauCeti.GlobalNumberFields.rayFundamentalDomain`: the points of `posRegion 𝔪` lying in one of
  the corresponding translates of Mathlib's fundamental cone.

## Main results

* `TauCeti.GlobalNumberFields.exists_unitsCongruenceSubgroup_smul_mem_rayFundamentalDomain`:
  every point of `posRegion 𝔪` of nonzero norm has a congruence-unit translate in the domain;
* `TauCeti.GlobalNumberFields.unitsCongruenceSubgroup_smul_mem_rayFundamentalDomain_iff_mem_torsion`
  — that translate is unique modulo the congruence units that are roots of unity;
* `TauCeti.GlobalNumberFields.index_unitsCongruenceSubgroup_mul_card_unitsCongruenceTorsion`:
  the index of the congruence units against that of their join with the roots of unity;
* `TauCeti.GlobalNumberFields.rayFundamentalDomain_one`: the trivial modulus recovers Mathlib's
  fundamental cone;
* `TauCeti.GlobalNumberFields.measurableSet_rayFundamentalDomain`: the domain is measurable;
* `TauCeti.GlobalNumberFields.smul_rayFundamentalDomain_inter_normLeOne`: the dilate by `c` of
  the norm-≤-one section is the norm-≤-`c ^ [K:ℚ]` section.

## References

The finite-union construction is the standard ray-class refinement of the fundamental cone; see
S. Lang, *Algebraic Number Theory*, Chapter VI, Section 2.

`smul_rayFundamentalDomain_inter_normLeOne` is adapted from
`github.com/CBirkbeck/aintlib` @ `2622c61d2502159c62865a1b59fc1de473519113` (Apache-2.0),
`projects/Chebotarev/CebotarevDensity/ForMathlib/IdealCongruenceCount.lean`, where
`cone_normLe_eq_smul_normLeOne` states it privately for the fundamental cone and the trivial
modulus under the stronger hypothesis `1 ≤ t`.
-/

 section

open NumberField NumberField.mixedEmbedding
open TauCeti.NumberField.Units

open scoped Pointwise

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-! ### The congruence units and the roots of unity -/







/-- The roots of unity lie in `unitsCongruenceSubgroupSupTorsion 𝔪`. -/
theorem torsion_le_unitsCongruenceSubgroupSupTorsion (𝔪 : Modulus K) :
    NumberField.Units.torsion K ≤ unitsCongruenceSubgroupSupTorsion 𝔪 :=
  le_sup_right









/-! ### The sign conditions prescribed by the infinite part -/



/-- `posRegion 𝔪` is the set of points positive at every real place of the infinite part of `𝔪`. -/
theorem posRegion_def (𝔪 : Modulus K) :
    posRegion 𝔪 = {x | ∀ w ∈ 𝔪.infinitePart, 0 < x.1 w} :=
  (rfl)















/-! ### The fundamental domain -/













/-- The ray fundamental domain is the positivity region intersected with the finite union of the
translates of Mathlib's fundamental cone by the chosen coset representatives. -/
theorem rayFundamentalDomain_eq_iUnion (𝔪 : Modulus K) :
    rayFundamentalDomain 𝔪 = posRegion 𝔪 ∩
      ⋃ q : (𝓞 K)ˣ ⧸ unitsCongruenceSubgroupSupTorsion 𝔪,
        rayUnitRepresentative 𝔪 q • fundamentalCone K := by
  ext x
  simp only [mem_rayFundamentalDomain_iff, Set.mem_inter_iff, Set.mem_iUnion,
    Set.mem_smul_set_iff_inv_smul_mem]































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
# Algebraic integers in the ray fundamental domain

Counting the integral ideals of a ray class goes through the points of the ray fundamental domain
that are images of algebraic integers.  This file introduces that carrier, `rayIntegerSet 𝔪`, and
the map recovering the integer a point comes from.

An element of `rayIntegerSet 𝔪` has a *unique* preimage in `𝓞 K`, because `mixedEmbedding` is
injective, and that preimage is nonzero, since the ray fundamental domain has no point of
vanishing norm (`norm_pos_of_mem_rayFundamentalDomain`).  The preimage is therefore recorded in
`(𝓞 K)⁰`, so that its nonzero-ness travels with the value.

For the trivial modulus this is Mathlib's `NumberField.mixedEmbedding.fundamentalCone.integerSet`.

The carrier also carries an action: a congruence unit sends a point of the domain back into the
domain exactly when it is a root of unity, so the roots of unity congruent to one modulo `𝔪` act
on `rayIntegerSet 𝔪`, and that action is free.  Counting a ray class will divide by the size of
its orbits, which is what makes freeness the fact worth isolating here.

## Main definitions

* `TauCeti.GlobalNumberFields.rayIntegerSet`: the points of the ray fundamental domain that are
  images of algebraic integers;
* `TauCeti.GlobalNumberFields.preimageOfMemRayIntegerSet`: the nonzero algebraic integer a point
  of `rayIntegerSet` is the image of;
* `TauCeti.GlobalNumberFields.unitsCongruenceTorsion`: the roots of unity congruent to one
  modulo `𝔪`, which act on `rayIntegerSet 𝔪`.

## Main results

* `TauCeti.GlobalNumberFields.mem_rayIntegerSet`: the defining membership condition;
* `TauCeti.GlobalNumberFields.mixedEmbedding_preimageOfMemRayIntegerSet`: the preimage map is a
  section of `mixedEmbedding`;
* `TauCeti.GlobalNumberFields.rayIntegerSet_one`: the trivial modulus recovers Mathlib's
  `integerSet`;
* `TauCeti.GlobalNumberFields.preimageOfMemRayIntegerSet_smul`: a congruence root of unity acts
  by multiplying the underlying algebraic integer;
* `TauCeti.GlobalNumberFields.stabilizer_rayIntegerSet_eq_bot`: the action is free, also
  available as an `IsCancelSMul` instance.

## References

* S. Lang, *Algebraic Number Theory*, Chapter VI, §2.
* `Mathlib/NumberTheory/NumberField/CanonicalEmbedding/FundamentalCone.lean`: the `integerSet`
  layer there — that set, its preimage API and its torsion action — is the model for
  `rayIntegerSet`, with the fundamental cone replaced by the ray fundamental domain and the full
  torsion group by the congruence torsion.
-/

 section

open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
open TauCeti.NumberField.Units

open scoped nonZeroDivisors

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

















/-! ### The free action of the congruence roots of unity -/







/-- A congruence root of unity acts on `rayIntegerSet 𝔪` by multiplying the underlying algebraic
integer. -/
@[simp]
theorem preimageOfMemRayIntegerSet_smul {𝔪 : Modulus K} (ζ : unitsCongruenceTorsion 𝔪)
    (a : rayIntegerSet 𝔪) :
    (preimageOfMemRayIntegerSet (ζ • a) : 𝓞 K) =
      ((ζ : (𝓞 K)ˣ) : 𝓞 K) * preimageOfMemRayIntegerSet a := by
  refine RingOfIntegers.ext <| mixedEmbedding_injective K ?_
  simp [mixedEmbedding_preimageOfMemRayIntegerSet,
    rayIntegerSetUnitsCongruenceTorsionSMul_smul_coe, unitSMul_smul]





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
# Elements of an ideal congruent to one, in the ray fundamental domain

For a modulus `𝔪` with finite part `𝔪₀` and a nonzero integral ideal `𝔞`, this file names the set
of points of the ray fundamental domain of `𝔪` that are images of elements of `𝔞` congruent to
one modulo `𝔪₀`, and records two descriptions of it.

Only the finite part appears in the set-builder: the conditions the infinite part imposes are
already carried by the ray fundamental domain, which lies in `posRegion 𝔪`
(`mem_posRegion_of_mem_rayFundamentalDomain`).

Nothing here asks that `𝔞` represent a given ray class, nor divides out the congruence roots of
unity acting on the domain; a ray-class ideal count imposes both itself.

## Main definitions

* `TauCeti.GlobalNumberFields.rayIdealSet`: the set described above;
* `TauCeti.GlobalNumberFields.rayIdealSetEquiv`: a bijection from it onto the points of
  `rayIntegerSet 𝔪` whose underlying algebraic integer lies in `𝔞` and is congruent to one
  modulo `𝔪₀`, with `rayIdealSetEquiv_apply` and `rayIdealSetEquiv_symm_apply` for the two
  directions.

## Main results

* `TauCeti.GlobalNumberFields.mem_rayIdealSet`: its points, unfolded;
* `TauCeti.GlobalNumberFields.rayIdealSet_one`: the trivial modulus recovers Mathlib's
  `NumberField.mixedEmbedding.fundamentalCone.idealSet`;
* `TauCeti.GlobalNumberFields.rayIdealSet_eq_inter_vadd`: the same set as a translate of the
  congruence lattice, intersected with the domain;
* `TauCeti.GlobalNumberFields.rayIdealSet_subset_rayIntegerSet` and
  `TauCeti.GlobalNumberFields.preimageOfMemRayIntegerSet_mem_and_sub_one_mem_of_mem_rayIdealSet`:
  its points lie in `rayIntegerSet 𝔪`, and the algebraic integer each of them is the image of
  lies in `𝔞` and is congruent to one modulo `𝔪₀`.

## Implementation notes

The set takes no base point, while its description as a translate does, which is why
`rayIdealSet_eq_inter_vadd` takes a witness `ξ`.  Taking `ξ = 0` would describe a different set
instead of dispensing with the witness: `coe_congruenceLattice_mk0_eq_image`
identifies `congruenceLattice 𝔪 (FractionalIdeal.mk0 K 𝔞)` with the image of `𝔞 * 𝔪₀`, and an
element of `𝔞 * 𝔪₀` congruent to one modulo `𝔪₀` forces `1 ∈ 𝔪₀`, so the two agree only for a
trivial finite part.

## References

* `Mathlib/NumberTheory/NumberField/CanonicalEmbedding/FundamentalCone.lean`: the `idealSet` and
  `idealSetEquiv` layer there is the model for this file, with the fundamental cone replaced by
  the ray fundamental domain and the congruence condition added.
-/

 section

open NumberField NumberField.mixedEmbedding

open scoped Pointwise nonZeroDivisors

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]







/-- **`rayIdealSet` as the domain met with a translate of the congruence lattice.**  For any
element `ξ` of `𝔞` congruent to one modulo `𝔪₀`, the set is the ray fundamental domain
intersected with the translate of `congruenceLattice 𝔪 (FractionalIdeal.mk0 K 𝔞)` by the image
of `ξ`.

The lattice on the right does not involve `ξ`, so a different witness only renames the translate;
and such a `ξ` exists exactly when `𝔞` and `𝔪₀` are coprime
(`Ideal.isCoprime_iff_exists_mem_and_sub_one_mem`).  Without one, `rayIdealSet 𝔪 𝔞` is empty. -/
theorem rayIdealSet_eq_inter_vadd (𝔪 : Modulus K) (𝔞 : (Ideal (𝓞 K))⁰) {ξ : 𝓞 K}
    (hξ𝔞 : ξ ∈ (𝔞 : Ideal (𝓞 K))) (hξ𝔪 : ξ - 1 ∈ 𝔪.finitePart) : rayIdealSet 𝔪 𝔞 =
      rayFundamentalDomain 𝔪 ∩ (mixedEmbedding K (ξ : K) +ᵥ
        (congruenceLattice 𝔪 (FractionalIdeal.mk0 K 𝔞) : Set (mixedSpace K))) := by
  rw [rayIdealSet, image_setOf_mem_and_sub_one_mem_eq_vadd_congruenceLattice 𝔪 𝔞 hξ𝔞 hξ𝔪]







/-- `rayIdealSetEquiv` leaves the underlying point of the mixed space unchanged; this is the ray
analogue of `NumberField.mixedEmbedding.fundamentalCone.idealSetEquiv_apply`. -/
@[simp]
theorem rayIdealSetEquiv_apply {𝔪 : Modulus K} {𝔞 : (Ideal (𝓞 K))⁰} (x : rayIdealSet 𝔪 𝔞) :
    ((rayIdealSetEquiv 𝔪 𝔞 x : rayIntegerSet 𝔪) : mixedSpace K) = (x : mixedSpace K) :=
  -- `(rfl)`, not `rfl`: this theorem is exported while `rayIdealSetEquiv` is not `@[expose]`,
  -- so a bare `rfl` is rejected as "not a definitional equality".
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
# Orbits of the congruence roots of unity on the ray integer set

Two points of `rayIntegerSet 𝔪` lie in the same orbit of the congruence roots of unity exactly
when some unit congruent to one modulo `𝔪` carries one to the other.  So orbits of the *small*
group `unitsCongruenceTorsion 𝔪` on the domain are the traces of the *large* group
`unitsCongruenceSubgroup 𝔪` acting on the whole space: the large group identifies no two points
of the domain that the small group does not already identify.  Together with
`exists_unitsCongruenceSubgroup_smul_mem_rayFundamentalDomain`, which moves each point of
nonzero norm in `posRegion 𝔪` into the domain, that is the sense in which the domain is
fundamental for the large group modulo the small one.

For the trivial modulus the large group is all of `(𝓞 K)ˣ`, translation by it is associatedness
in `(𝓞 K)⁰`, and the statement is Mathlib's `integerSetToAssociates_eq_iff`, whose left-hand side
reads the orbit off in `Associates (𝓞 K)⁰`.  Mathlib has no such quotient type for a proper
subgroup of the units, so this file states the orbit relation directly.

## Main results

* `TauCeti.GlobalNumberFields.exists_mem_unitsCongruenceTorsion_smul_iff`: the orbit relation for
  any two points of the domain;
* `TauCeti.GlobalNumberFields.exists_unitsCongruenceTorsion_smul_iff`: the same on
  `rayIntegerSet 𝔪`, which is the form the count consumes.
-/

 section

open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone

open scoped nonZeroDivisors

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- **The orbit relation, for any two points of the domain.**  A congruence unit carrying one
point of `rayFundamentalDomain 𝔪` to another is automatically a root of unity, so the two
subgroups have the same orbits on the domain.  Only membership of the domain is needed; the
points need not be images of algebraic integers. -/
theorem exists_mem_unitsCongruenceTorsion_smul_iff {𝔪 : Modulus K} {a b : mixedSpace K}
    (ha : a ∈ rayFundamentalDomain 𝔪) (hb : b ∈ rayFundamentalDomain 𝔪) :
    (∃ ζ ∈ unitsCongruenceTorsion 𝔪, ζ • a = b) ↔
      ∃ u ∈ unitsCongruenceSubgroup 𝔪, u • a = b := by
  refine ⟨fun ⟨ζ, hζ, h⟩ ↦ ⟨ζ, (mem_unitsCongruenceTorsion.mp hζ).1, h⟩, fun ⟨u, hu, hsmul⟩ ↦ ?_⟩
  -- the unit is constrained only by a congruence; membership of both points in the domain is
  -- what upgrades it to a root of unity
  exact ⟨u, mem_unitsCongruenceTorsion.mpr ⟨hu,
    (unitsCongruenceSubgroup_smul_mem_rayFundamentalDomain_iff_mem_torsion ha hu).mp
      (hsmul ▸ hb)⟩, hsmul⟩

/-- **The orbit relation on the ray integer set.**  Two points of `rayIntegerSet 𝔪` lie in one
orbit of the congruence roots of unity exactly when some unit congruent to one modulo `𝔪` carries
one to the other in the mixed space.  Since `mixedEmbedding` is injective and multiplicative, that
is the same as their algebraic integers differing by such a unit, which is the form the ray class
count consumes. -/
theorem exists_unitsCongruenceTorsion_smul_iff {𝔪 : Modulus K} (a b : rayIntegerSet 𝔪) :
    (∃ ζ : unitsCongruenceTorsion 𝔪, ζ • a = b) ↔
      ∃ u ∈ unitsCongruenceSubgroup 𝔪, u • (a : mixedSpace K) = (b : mixedSpace K) := by
  rw [← exists_mem_unitsCongruenceTorsion_smul_iff (mem_rayIntegerSet.mp a.prop).1
    (mem_rayIntegerSet.mp b.prop).1]
  exact ⟨fun ⟨⟨ζ, hζ⟩, h⟩ ↦ ⟨ζ, hζ, by simpa using congrArg Subtype.val h⟩,
    fun ⟨ζ, hζ, h⟩ ↦ ⟨⟨ζ, hζ⟩, Subtype.ext (by simpa using h)⟩⟩

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
# Counting ideals of trivial ray class by points of the ray fundamental domain

Let `𝔪` be a modulus of a number field `K` and `𝔞` a nonzero integral ideal prime to `𝔪`.  This
file matches the integral ideals prime to `𝔪` that are multiples of `𝔞`, have trivial ray class
and have norm at most `s`, against the points of `rayIdealSet 𝔪 𝔞` of mixed norm at most `s`:
each such ideal accounts for exactly `Nat.card (unitsCongruenceTorsion 𝔪)` points.

The correspondence sends a point to the ideal generated by the algebraic integer it is the image
of; the generator criterion `idealClass_eq_one_iff_exists_generator` identifies the ideals of
trivial ray class as exactly those arising this way.

## Main results

* `TauCeti.GlobalNumberFields.card_idealClass_eq_one_dvd_norm_le`: the number of multiples of `𝔞`
  prime to `𝔪` of trivial ray class and norm at most `s`, times the number of roots of unity
  congruent to one modulo `𝔪`, is the number of points of `rayIdealSet 𝔪 𝔞` of mixed norm at
  most `s`.
-/

 section

open NumberField NumberField.mixedEmbedding

open scoped nonZeroDivisors

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]







/-- **Two points generating the same ideal lie in one orbit.**  If the algebraic integers under
two points of `rayIntegerSet 𝔪` are congruent to one modulo `𝔪₀` and generate the same ideal,
some congruence root of unity carries one point to the other. -/
private theorem exists_smul_eq_of_span_eq {𝔪 : Modulus K} {a b : rayIntegerSet 𝔪}
    (ha : (preimageOfMemRayIntegerSet a : 𝓞 K) - 1 ∈ 𝔪.finitePart)
    (hb : (preimageOfMemRayIntegerSet b : 𝓞 K) - 1 ∈ 𝔪.finitePart)
    (h : Ideal.span {(preimageOfMemRayIntegerSet a : 𝓞 K)} =
      Ideal.span {(preimageOfMemRayIntegerSet b : 𝓞 K)}) :
    ∃ ζ : unitsCongruenceTorsion 𝔪, ζ • a = b := by
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp h
  -- `u - 1 = (β - 1) - u (α - 1)` for the generators `α`, `β` of `a`, `b`, with `β = α u`
  have hu1 : (u : 𝓞 K) - 1 ∈ 𝔪.finitePart := by
    simpa [← hu, mul_sub, mul_comm] using sub_mem hb (Ideal.mul_mem_left _ (u : 𝓞 K) ha)
  -- `u` has the sign of `β / α`, which is positive at the real places of `𝔪`
  have hupos : ∀ w ∈ 𝔪.infinitePart,
      0 < InfinitePlace.embedding_of_isReal w.2 (algebraMap (𝓞 K) K u) := fun w hw ↦
    (pos_iff_pos_of_mul_pos (by simpa [← hu] using pos_preimageOfMemRayIntegerSet b hw)).mp
      (pos_preimageOfMemRayIntegerSet a hw)
  refine (exists_unitsCongruenceTorsion_smul_iff a b).mpr ⟨u,
    mem_unitsCongruenceSubgroup.mpr (isCongrOne_of_sub_one_mem (by simp) hu1 hupos), ?_⟩
  grind [unitSMul_smul, mixedEmbedding_preimageOfMemRayIntegerSet]

variable (𝔪 : Modulus K) (𝔞 : integralIdealsPrimeTo 𝔪) (s : ℝ)





variable {𝔪 𝔞 s}







/-- The congruence roots of unity act simply transitively on each fibre of `toIdeal`. -/
private noncomputable def fiberEquiv (I : IdealCountSet 𝔪 𝔞 s) :
    unitsCongruenceTorsion 𝔪 ≃ {a : PointSet 𝔪 𝔞 s // toIdeal a = I} :=
  let a₀ := (exists_toIdeal_eq I).choose
  have ha₀ := toIdeal_eq_iff.mp (exists_toIdeal_eq I).choose_spec
  have hpre (ζ : unitsCongruenceTorsion 𝔪) := preimageOfMemRayIntegerSet_smul ζ a₀.1
  Equiv.ofBijective (fun ζ ↦ ⟨⟨ζ • a₀.1, ⟨hpre ζ ▸ Ideal.mul_mem_left _ _ a₀.2.1.1,
        hpre ζ ▸ unit_mul_sub_one_mem (mem_unitsCongruenceTorsion.mp ζ.2).1 a₀.2.1.2⟩,
        (norm_unit_smul ζ.1 _).trans_le a₀.2.2⟩,
      toIdeal_eq_iff.mpr <| by rw [hpre, Ideal.span_singleton_mul_left_unit ζ.1.isUnit, ha₀]⟩)
    ⟨fun ζ ζ' h ↦ IsCancelSMul.right_cancel ζ ζ' a₀.1 congr($h.1.1), fun b ↦
      (exists_smul_eq_of_span_eq a₀.2.1.2 b.1.2.1.2 (ha₀.trans (toIdeal_eq_iff.mp b.2).symm)).imp
        fun _ hζ ↦ Subtype.ext (Subtype.ext hζ)⟩

/-- **Ideals of trivial ray class, counted by points of the ray fundamental domain.**  For a
nonzero integral ideal `𝔞` prime to `𝔪`, the number of integral ideals prime to `𝔪` that are
multiples of `𝔞`, have trivial ray class and have norm at most `s`, multiplied by the number of
roots of unity congruent to one modulo `𝔪`, is the number of points of `rayIdealSet 𝔪 𝔞` of mixed
norm at most `s`.

This is the ray analogue of
`NumberField.mixedEmbedding.fundamentalCone.card_isPrincipal_dvd_norm_le`.  The left-hand count is
the one `rayClassIdealCountingFunction_eq_card_dvd_and_idealClass_eq_one` reduces the ray class
counting function to, with `s` the scaled bound there. -/
theorem card_idealClass_eq_one_dvd_norm_le (𝔪 : Modulus K) (𝔞 : integralIdealsPrimeTo 𝔪)
    (s : ℝ) :
    Nat.card {I : integralIdealsPrimeTo 𝔪 // 𝔞 ∣ I ∧ idealClass 𝔪 I = 1 ∧
        (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ s} * Nat.card (unitsCongruenceTorsion 𝔪) =
      Nat.card {a : rayIdealSet 𝔪 ⟨𝔞, mem_nonZeroDivisors_of_ne_zero
          (NumberFieldArithmetic.mem_integralIdealsAway_iff.mp 𝔞.prop).1⟩ //
        mixedEmbedding.norm (a : mixedSpace K) ≤ s} := by
  rw [← Nat.card_prod]
  refine Nat.card_congr ?_
  calc _ ≃ Σ _ : IdealCountSet 𝔪 𝔞 s, unitsCongruenceTorsion 𝔪 := (Equiv.sigmaEquivProd _ _).symm
    _ ≃ PointSet 𝔪 𝔞 s :=
      (Equiv.sigmaCongrRight fiberEquiv).trans (Equiv.sigmaFiberEquiv toIdeal)
    _ ≃ _ := (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm.trans
      ((rayIdealSetEquiv 𝔪 ⟨𝔞, mem_nonZeroDivisors_of_ne_zero
        (NumberFieldArithmetic.mem_integralIdealsAway_iff.mp 𝔞.prop).1⟩).subtypeEquiv
          fun a ↦ by rw [rayIdealSetEquiv_apply]).symm

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
# A Lipschitz parametrization of the frontier of the ray fundamental domain

`TauCeti.NumberTheory.GeometryOfNumbers.LatticePointCount` counts lattice points in a dilated
region with a power-saving error term, but only for regions whose frontier is Lipschitz
parametrizable in codimension one. `NormLeOneLipschitz` discharges that hypothesis for Mathlib's
`normLeOne K`, the norm-≤-one section of the fundamental cone. This file lifts it to the section
`rayFundamentalDomain 𝔪 ∩ {x | mixedEmbedding.norm x ≤ 1}` of the ray fundamental domain of an
arbitrary modulus, which is the region whose lattice points count the algebraic integers in a
fixed ray class.

`rayFundamentalDomain_inter_normLeOne_eq` presents that section as `posRegion 𝔪 ∩ A`, where
`A = ⋃ q, rayUnitRepresentative 𝔪 q • normLeOne K` is a *finite* union of unit translates: the
unit action preserves the mixed norm, so it commutes with the norm condition.

The two factors are of opposite character. `A` is bounded, with a complicated boundary;
`posRegion 𝔪` is an unbounded finite intersection of open half spaces, with a boundary made of
hyperplanes. So the naive `frontier (A ∩ B) ⊆ frontier A ∪ frontier B` is useless here: the
frontier of `posRegion 𝔪` is unbounded, and a Lipschitz-parametrizable set is a finite union of
Lipschitz images of a compact cube, hence bounded — so that union is parametrizable in no
dimension whatsoever. Mathlib's sharp form `frontier_inter_subset` keeps each frontier paired
with the closure of the *other* factor, and that pairing is what makes the argument work:

* `frontier A ∩ closure (posRegion 𝔪)` lies in `frontier A`, which lies in the union of the
  frontiers of the finitely many translates; each `frontier (u • normLeOne K)` is a Lipschitz
  image of `frontier (normLeOne K)`, because a unit acts by a homeomorphism;
* `closure A ∩ frontier (posRegion 𝔪)` is a *bounded* subset of finitely many coordinate
  hyperplanes, and a bounded subset of a hyperplane is Lipschitz parametrizable in codimension
  one (`TauCeti.IsLipschitzParametrizable.of_isBounded_of_subset_ker`).

## Main results

* `TauCeti.GlobalNumberFields.isLipschitzParametrizable_frontier_rayFundamentalDomain`: the
  norm-≤-one section of the ray fundamental domain is bounded and measurable, and its frontier is
  Lipschitz parametrizable in dimension `finrank ℝ (mixedSpace K) - 1`, which is `[K:ℚ] - 1` by
  `mixedEmbedding.finrank`. These are exactly the three hypotheses the lattice-point count with a
  power-saving error consumes, so they are stated together;
* `TauCeti.GlobalNumberFields.isBounded_rayFundamentalDomain_inter_normLeOne` and
  `TauCeti.GlobalNumberFields.measurableSet_rayFundamentalDomain_inter_normLeOne`: the first two
  conclusions on their own, for callers that need only one of them;
* `TauCeti.GlobalNumberFields.rayFundamentalDomain_inter_normLeOne_eq`: that section is the
  positivity region cut by a finite union of unit translates of `normLeOne K`;
* `TauCeti.GlobalNumberFields.frontier_posRegion_subset`: the frontier of the positivity region
  lies in the coordinate hyperplanes prescribed by the infinite part of the modulus.

## References

* C. Birkbeck, [*AINTLIB*](https://github.com/CBirkbeck/AINTLIB) at commit
  `db14b34cc5e3d79603e67c205dfa86b7b989000c` (Apache-2.0),
  `projects/Chebotarev/CebotarevDensity/ForMathlib/IdealCongruenceCount.lean`, which carries out
  the same argument for a sign orthant cut out of a bounded region of `ι → ℝ`:
  `frontier_posRegion_subset` here is that file's `frontier_signOrthant_subset`, and
  `isLipschitzParametrizable_frontier_rayFundamentalDomain` follows its
  `exists_frontier_cover_inter_orthant`, including the use of `frontier_inter_subset` to pair each
  frontier with the other factor's closure. The bounded hyperplane pieces are handled here by the
  general `TauCeti.IsLipschitzParametrizable.of_isBounded_of_subset_ker` rather than by that
  file's explicit slab chart `exists_lipschitz_cube_cover_hyperplane_slab`.
-/

 section

open Module NumberField NumberField.mixedEmbedding
  NumberField.mixedEmbedding.fundamentalCone
open scoped Pointwise

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]







/-- **The norm-≤-one section of the ray fundamental domain**, as the positivity region cut by a
finite union of unit translates of Mathlib's norm-≤-one region. The unit action preserves the
mixed norm, so it commutes with the norm condition. -/
theorem rayFundamentalDomain_inter_normLeOne_eq (𝔪 : Modulus K) :
    rayFundamentalDomain 𝔪 ∩ {x : mixedSpace K | mixedEmbedding.norm x ≤ 1} =
      posRegion 𝔪 ∩ ⋃ q : (𝓞 K)ˣ ⧸ unitsCongruenceSubgroupSupTorsion 𝔪,
        rayUnitRepresentative 𝔪 q • normLeOne K := by
  ext x
  simp only [rayFundamentalDomain_eq_iUnion, Set.mem_inter_iff, Set.mem_iUnion,
    Set.mem_smul_set_iff_inv_smul_mem, Set.mem_ofPred_eq, norm_unit_smul]
  tauto











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
# Reflecting real coordinates preserves the fundamental cone

Membership in Mathlib's `NumberField.mixedEmbedding.fundamentalCone K` depends on a point only
through its norms at the infinite places, and so does its mixed norm. Reflecting the real
coordinates at a set of real places with `negAt` changes none of these norms, so it preserves the
fundamental cone and every unit translate of the norm-≤-one region `normLeOne K`.

## Main results

* `TauCeti.NumberField.mixedEmbedding.negAt_mem_fundamentalCone_iff`: `negAt s x` lies in the
  fundamental cone exactly when `x` does.
* `TauCeti.NumberField.mixedEmbedding.negAt_mem_unit_smul_normLeOne_iff`: the same for the
  translate `u • normLeOne K` by a unit `u`.
-/

 section

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped Pointwise

namespace TauCeti.NumberField.mixedEmbedding

variable {K : Type*} [Field K] [NumberField K]



/-- Reflecting real coordinates preserves each unit translate of `normLeOne K`, since it commutes
with the unit action. -/
@[simp]
theorem negAt_mem_unit_smul_normLeOne_iff (s : Set {w : InfinitePlace K // w.IsReal})
    (u : (𝓞 K)ˣ) (x : mixedSpace K) :
    negAt s x ∈ u • fundamentalCone.normLeOne K ↔ x ∈ u • fundamentalCone.normLeOne K := by
  simp only [Set.mem_smul_set_iff_inv_smul_mem, unitSMul_smul, fundamentalCone.mem_normLeOne,
    map_mul, norm_negAt]
  refine and_congr_left fun _ ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩ <;>
    exact fundamentalCone.mem_of_normAtPlace_eq h fun w ↦ by simp [map_mul, normAtPlace_negAt]

end TauCeti.NumberField.mixedEmbedding

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
# The volume of the norm-one section of the ray fundamental domain

On the section of norm at most one, the ray fundamental domain of a modulus `𝔪` is the part of
the union of the unit translates of Mathlib's `fundamentalCone.normLeOne K` that carries the
signs prescribed by the infinite part of `𝔪`. The translates are indexed by the cosets of
`unitsCongruenceSubgroupSupTorsion 𝔪`; they are pairwise disjoint and each has the volume of
`normLeOne K`, and their union is stable under reflection at every real place. Prescribing the
sign at the `s` real places of the infinite part therefore divides the volume of the union by
`2 ^ s`.

## Main results

* `TauCeti.GlobalNumberFields.two_pow_mul_volume_rayFundamentalDomain_inter_normLeOne`:
  `2 ^ s` times the volume of the norm-one section of `rayFundamentalDomain 𝔪` is the index of
  `unitsCongruenceSubgroupSupTorsion 𝔪` times the volume of `normLeOne K`.
* `TauCeti.GlobalNumberFields.measureReal_rayFundamentalDomain_inter_normLeOne`: the same
  volume as an explicit real number, the index times `2 ^ r₁ · π ^ r₂ · Reg_K / 2 ^ s`.

## References

* S. Lang, *Algebraic Number Theory*, Chapter VI, §2.
-/

 section

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open NumberField.mixedEmbedding.fundamentalCone TauCeti.NumberField.mixedEmbedding
open NumberField.Units
open scoped Pointwise Real

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

private theorem pairwise_disjoint_rayUnitRepresentative_smul_normLeOne (𝔪 : Modulus K) :
    Pairwise (Function.onFun Disjoint fun q ↦ rayUnitRepresentative 𝔪 q • normLeOne K) := by
  refine fun q q' hqq' ↦ Set.disjoint_left.mpr fun x hx hx' ↦ hqq' ?_
  rw [Set.mem_smul_set_iff_inv_smul_mem] at hx hx'
  -- two representatives carrying the same point into the cone differ by a root of unity
  rw [← rayUnitRepresentative_mk 𝔪 q, ← rayUnitRepresentative_mk 𝔪 q', QuotientGroup.eq]
  refine torsion_le_unitsCongruenceSubgroupSupTorsion 𝔪 <|
    (fundamentalCone.unit_smul_mem_iff_mem_torsion hx'.1 _).mp ?_
  rw [mul_smul, smul_inv_smul]
  exact hx.1

open scoped Classical in
/-- **The volume of the norm-≤-one section of the ray fundamental domain.**  With `s` real places
in the infinite part of `𝔪`, the section of `rayFundamentalDomain 𝔪` of norm at most one has
`1 / 2 ^ s` of the volume of Mathlib's `normLeOne K` for each coset of
`unitsCongruenceSubgroupSupTorsion 𝔪`; the statement clears the denominator `2 ^ s`. For the
trivial modulus both factors are one, and the section has the volume of `normLeOne K`. -/
theorem two_pow_mul_volume_rayFundamentalDomain_inter_normLeOne (𝔪 : Modulus K) :
    2 ^ 𝔪.infinitePart.card * volume (rayFundamentalDomain 𝔪 ∩ {x | mixedEmbedding.norm x ≤ 1}) =
      (unitsCongruenceSubgroupSupTorsion 𝔪).index * volume (normLeOne K) := by
  have hm (q) : MeasurableSet (rayUnitRepresentative 𝔪 q • normLeOne K) :=
    (measurableSet_normLeOne K).const_smul _
  -- the union of the translates is stable under reflection at each real place, so the sign cut
  -- divides its volume by `2 ^ s`; the translates are disjoint, each with the volume of
  -- `normLeOne K`
  rw [rayFundamentalDomain_inter_normLeOne_eq, Set.inter_comm, posRegion_def,
    ← volume_eq_two_pow_mul_volume_inter_pos _ (by simp) (.iUnion hm),
    measure_iUnion (pairwise_disjoint_rayUnitRepresentative_smul_normLeOne 𝔪) hm]
  simp [ENat.card_eq_coe_natCard, Subgroup.index]

open scoped Classical in
/-- **The real volume of the norm-≤-one section of the ray fundamental domain.**  With `s` real
places in the infinite part of `𝔪`, the section of `rayFundamentalDomain 𝔪` of norm at most one
has real volume `i · 2 ^ r₁ · π ^ r₂ · Reg_K / 2 ^ s`, where `i` is the index of
`unitsCongruenceSubgroupSupTorsion 𝔪`, `r₁` and `r₂` are the numbers of real and complex places
of `K`, and `Reg_K` is its regulator. -/
theorem measureReal_rayFundamentalDomain_inter_normLeOne (𝔪 : Modulus K) :
    volume.real (rayFundamentalDomain 𝔪 ∩ {x | mixedEmbedding.norm x ≤ 1}) =
      (unitsCongruenceSubgroupSupTorsion 𝔪).index *
        (2 ^ nrRealPlaces K * π ^ nrComplexPlaces K * regulator K) / 2 ^ 𝔪.infinitePart.card := by
  rw [eq_div_iff (by positivity), mul_comm, measureReal_def]
  simpa [volume_normLeOne, (regulator_pos K).le] using
    congrArg ENNReal.toReal (two_pow_mul_volume_rayFundamentalDomain_inter_normLeOne 𝔪)

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
# The ray class number formula

Let `𝔪` be a modulus of a number field `K`, and write
`A 𝔪 = (𝓞 K ⧸ 𝔪.finitePart)ˣ × (𝔪.infinitePart → ℤˣ)` for its residue units and prescribed signs.
The exact sequence constructed in `TauCeti.NumberTheory.NumberField.Global.RayClass.Exact` is

```text
1 → unitsCongruenceSubgroup 𝔪 → (𝓞 K)ˣ → A 𝔪 → RayClassGroup 𝔪 → ClassGroup (𝓞 K) → 1
```

and this file reads off the ray class number formula

```text
#(RayClassGroup 𝔪) * [(𝓞 K)ˣ : unitsCongruenceSubgroup 𝔪]
  = #(ClassGroup (𝓞 K)) * #(𝓞 K ⧸ 𝔪.finitePart)ˣ * 2 ^ #𝔪.infinitePart.
```

The right-hand tail `A 𝔪 → RayClassGroup 𝔪 → ClassGroup (𝓞 K) → 1` refines the exact tail of
`TauCeti.NumberTheory.NumberField.Global.RayClass.Exact`, whose left-hand term is the larger group
`primeToSubgroup 𝔪`: by `residueSignEquiv`, the principal ray class of an element prime to `𝔪`
depends only on its residue and its signs, so `principalRayClass 𝔪` descends to `A 𝔪`.

The left-hand part is the unit obstruction.  An element prime to `𝔪` has trivial principal ray
class exactly when it becomes congruent to one after multiplication by a global unit
(`principalRayClass_eq_one_iff`), so the kernel of `A 𝔪 → RayClassGroup 𝔪` is the image of the
integer units, and the kernel of `(𝓞 K)ˣ → A 𝔪` is the group of units congruent to one.  That image
is what glues the residue units, the signs and the ordinary class group together inside the ray
class group; in general `RayClassGroup 𝔪` is not the product of the three.

At the narrow modulus the residue factor is trivial and the formula becomes
`#(RayClassGroup (narrowModulus K)) * [(𝓞 K)ˣ : (𝓞 K)ˣ⁺] = #(ClassGroup (𝓞 K)) * 2 ^ r₁`, with
`(𝓞 K)ˣ⁺` the totally positive units and `r₁` the number of real places.

## Main results

* `TauCeti.GlobalNumberFields.card_ker_rayClassToClassGroup_mul_index`: the order of the kernel of
  `RayClassGroup 𝔪 → ClassGroup (𝓞 K)`.
* `TauCeti.GlobalNumberFields.card_rayClassGroup_mul_index` and
  `TauCeti.GlobalNumberFields.card_rayClassGroup`: the ray class number formula.
* `TauCeti.GlobalNumberFields.card_rayClassGroup_narrowModulus_mul_index`: its narrow case.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, (1.10) and (1.11).
* S. Lang, *Algebraic Number Theory*, Chapter VI, §1, Theorem 1.
-/

 section

open IsDedekindDomain NumberField
open scoped nonZeroDivisors NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-! ### The ray class number formula -/

/-- **The order of the kernel of `RayClassGroup 𝔪 → ClassGroup (𝓞 K)`.**  The kernel is the group of
residue units and sign patterns modulo the image of the integer units, and that image has order the
index of the units congruent to one. -/
theorem card_ker_rayClassToClassGroup_mul_index (𝔪 : Modulus K) :
    Nat.card (rayClassToClassGroup 𝔪).ker * (unitsCongruenceSubgroup 𝔪).index =
      Nat.card (𝓞 K ⧸ 𝔪.finitePart)ˣ * 2 ^ 𝔪.infinitePart.card := by
  -- The image of the units has order the index of its kernel, and the residue units and signs
  -- are counted by the index of the kernel of the (surjective) residue-and-sign presentation.
  have hunits : Nat.card (unitsResidueSignHom 𝔪).range = (unitsCongruenceSubgroup 𝔪).index := by
    rw [← Subgroup.index_ker, ker_unitsResidueSignHom]
  have hA : Nat.card ((𝓞 K ⧸ 𝔪.finitePart)ˣ × (𝔪.infinitePart → ℤˣ)) =
      Nat.card (𝓞 K ⧸ 𝔪.finitePart)ˣ * 2 ^ 𝔪.infinitePart.card := by
    rw [← relIndex_congruenceSubgroup, Subgroup.relIndex, ← ker_residueSignHom, Subgroup.index_ker,
      MonoidHom.range_eq_top.mpr (residueSignHom_surjective 𝔪), Subgroup.card_top]
  rw [← range_residueSignRayClass, ← hunits, ← hA, ← (residueSignRayClass 𝔪).ker.card_mul_index,
    Subgroup.index_ker, ker_residueSignRayClass, mul_comm]

/-- **The ray class number formula.**  The order of the ray class group, times the index of the
units congruent to one modulo `𝔪`, is the class number times the number of residue units modulo the
finite part times two for each real place of the infinite part. -/
theorem card_rayClassGroup_mul_index (𝔪 : Modulus K) :
    Nat.card (RayClassGroup 𝔪) * (unitsCongruenceSubgroup 𝔪).index =
      Nat.card (ClassGroup (𝓞 K)) *
        (Nat.card (𝓞 K ⧸ 𝔪.finitePart)ˣ * 2 ^ 𝔪.infinitePart.card) := by
  rw [← card_ker_rayClassToClassGroup_mul_index, ← (rayClassToClassGroup 𝔪).ker.card_mul_index,
    Subgroup.index_ker, MonoidHom.range_eq_top.mpr (rayClassToClassGroup_surjective 𝔪),
    Subgroup.card_top]
  ring





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
# Euler's totient for ideals of a Dedekind domain

For an ideal `I` of an infinite Dedekind domain `R` whose quotient `R ⧸ I` is finite, this file
counts the units of `R ⧸ I` in terms of the absolute norm `N = Ideal.absNorm`:
`#(R ⧸ I)ˣ = N I · ∏_{𝔭 ∣ I} (1 - (N 𝔭)⁻¹)`, the product running over the height-one primes
dividing `I`. For `R = ℤ` this is Euler's product formula for the totient.

The set of primes dividing `I` is passed as a `Finset` `S` together with the characterisation
`∀ v, v ∈ S ↔ v.asIdeal ∣ I`, so that any concrete description of the prime divisors of `I` can
be used directly.

## Main results

* `Ideal.card_units_quotient_pow_mul_absNorm`: `#(R ⧸ P ^ e)ˣ · N P = N (P ^ e) · (N P - 1)` for a
  maximal ideal `P` and `e ≠ 0`.
* `Ideal.card_units_quotient_mul_prod_absNorm`: `#(R ⧸ I)ˣ · ∏_{𝔭 ∈ S} N 𝔭 = N I · ∏_{𝔭 ∈ S}
  (N 𝔭 - 1)` in `ℕ`, the analogue of `Nat.totient_mul_prod_primeFactors`.
* `Ideal.card_units_quotient_eq_absNorm_mul_prod`: `#(R ⧸ I)ˣ = N I · ∏_{𝔭 ∈ S} (1 - (N 𝔭)⁻¹)`
  in any field of characteristic zero, the analogue of `Nat.totient_eq_mul_prod_factors`.
-/

 section

open IsDedekindDomain

namespace Ideal

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Infinite R] [Module.Free ℤ R]



private theorem card_units_quotient_mul_prod_absNorm_of_prod_eq (I : Ideal R) [Finite (R ⧸ I)]
    {S : Finset (HeightOneSpectrum R)} {e : HeightOneSpectrum R → ℕ} (he : ∀ v ∈ S, e v ≠ 0)
    (hprod : ∏ v ∈ S, v.asIdeal ^ e v = I) : Nat.card (R ⧸ I)ˣ * ∏ v ∈ S, absNorm v.asIdeal =
      absNorm I * ∏ v ∈ S, (absNorm v.asIdeal - 1) := by
  let φ := HeightOneSpectrum.quotientEquivPiOfProdEq I (fun v : S ↦ (v : HeightOneSpectrum R))
    (fun v ↦ e v) Subtype.coe_injective.pairwise_ne ((Finset.prod_coe_sort S _).trans hprod)
  rw [Nat.card_congr ((Units.mapEquiv φ.toMulEquiv).trans MulEquiv.piUnits).toEquiv, Nat.card_pi,
    Finset.prod_coe_sort S fun v ↦ Nat.card (R ⧸ v.asIdeal ^ e v)ˣ, ← hprod, map_prod,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v hv ↦ ?_
  have : Finite (R ⧸ v.asIdeal ^ e v) :=
    Finite.of_surjective _ ((Function.surjective_eval (⟨v, hv⟩ : S)).comp φ.surjective)
  exact card_units_quotient_pow_mul_absNorm v.asIdeal (he v hv)

/-- **Euler's totient for ideals**, multiplicative form: if `S` is the set of height-one primes
dividing `I` and `R ⧸ I` is finite, then `#(R ⧸ I)ˣ · ∏_{𝔭 ∈ S} N 𝔭 = N I · ∏_{𝔭 ∈ S} (N 𝔭 - 1)`.
This is the analogue of `Nat.totient_mul_prod_primeFactors`; for the form with the factors
`1 - (N 𝔭)⁻¹` in a field, see `Ideal.card_units_quotient_eq_absNorm_mul_prod`. -/
theorem card_units_quotient_mul_prod_absNorm (I : Ideal R) [Finite (R ⧸ I)]
    {S : Finset (HeightOneSpectrum R)} (hS : ∀ v, v ∈ S ↔ v.asIdeal ∣ I) :
    Nat.card (R ⧸ I)ˣ * ∏ v ∈ S, absNorm v.asIdeal =
      absNorm I * ∏ v ∈ S, (absNorm v.asIdeal - 1) := by
  have hI : I ≠ 0 := fun h ↦ (absNorm_ne_zero_iff I).mpr ‹_› (by rw [h, map_zero])
  let e : HeightOneSpectrum R → ℕ := fun v ↦
    (Associates.mk v.asIdeal).count (Associates.mk I).factors
  have he (v : HeightOneSpectrum R) : e v ≠ 0 ↔ v ∈ S := by
    rw [hS, Associates.count_ne_zero_iff_dvd hI v.irreducible]
  refine card_units_quotient_mul_prod_absNorm_of_prod_eq I (fun v ↦ (he v).mpr) ?_
  rw [← finprod_eq_finsetProd_of_mulSupport_subset (fun v ↦ v.asIdeal ^ e v) fun v hv ↦
    (he v).mp fun h ↦ hv (by simp [h])]
  exact Ideal.finprod_heightOneSpectrum_factorization hI

/-- **Euler's totient for ideals**: if `S` is the set of height-one primes dividing `I` and
`R ⧸ I` is finite, then `#(R ⧸ I)ˣ = N I · ∏_{𝔭 ∈ S} (1 - (N 𝔭)⁻¹)` in any field of
characteristic zero. This is the analogue of `Nat.totient_eq_mul_prod_factors`, which is stated
over `ℚ` only; the identity in `ℕ`, free of inverses, is
`Ideal.card_units_quotient_mul_prod_absNorm`. -/
theorem card_units_quotient_eq_absNorm_mul_prod {F : Type*} [Field F] [CharZero F] (I : Ideal R)
    [Finite (R ⧸ I)] {S : Finset (HeightOneSpectrum R)} (hS : ∀ v, v ∈ S ↔ v.asIdeal ∣ I) :
    (Nat.card (R ⧸ I)ˣ : F) = absNorm I * ∏ v ∈ S, (1 - (absNorm v.asIdeal : F)⁻¹) := by
  have hN (v) (hv : v ∈ S) : absNorm v.asIdeal ≠ 0 :=
    ne_zero_of_dvd_ne_zero ((absNorm_ne_zero_iff I).mpr ‹_›) (map_dvd absNorm ((hS v).mp hv))
  have hN' (v) (hv : v ∈ S) : (absNorm v.asIdeal : F) ≠ 0 := Nat.cast_ne_zero.mpr (hN v hv)
  have key (v) (hv : v ∈ S) :
      (1 - (absNorm v.asIdeal : F)⁻¹) * absNorm v.asIdeal = (absNorm v.asIdeal - 1 : ℕ) := by
    rw [sub_mul, one_mul, inv_mul_cancel₀ (hN' v hv), Nat.cast_pred (Nat.pos_of_ne_zero (hN v hv))]
  refine mul_right_cancel₀ (Finset.prod_ne_zero_iff.mpr hN') ?_
  rw [mul_assoc, ← Finset.prod_mul_distrib, Finset.prod_congr rfl key]
  exact_mod_cast card_units_quotient_mul_prod_absNorm I hS

end Ideal

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
# The geometric coefficient of the ray ideal count

Counting the points of a coset of `congruenceLattice 𝔪 (mk0 𝔞)` in the norm-`≤ t` section of
`rayFundamentalDomain 𝔪` gives a main term `V / covol · t`, where `V` is the volume of the
norm-one section of the domain and `covol` the covolume of the lattice. This file evaluates the
coefficient `V / covol · N 𝔞` that this produces for the ideals of a ray class, where
`t = x · N 𝔞`, in terms of `rayClassIdealMainTerm 𝔪`.

Writing `w_𝔪` for the number of roots of unity congruent to one modulo `𝔪`, the coefficient is
`V / covol · N 𝔞 = w_𝔪 · rayClassIdealMainTerm 𝔪`.

## Main results

* `TauCeti.GlobalNumberFields.measureReal_div_covolume_congruenceLattice_mul_absNorm`: the
  coefficient is `w_𝔪` times `rayClassIdealMainTerm 𝔪`.
-/

 section

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open NumberField.mixedEmbedding.fundamentalCone NumberField.Units
open scoped nonZeroDivisors Real

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

private theorem card_unitsCongruenceTorsion_mul_rayClassIdealMainTerm (𝔪 : Modulus K) :
    Nat.card (unitsCongruenceTorsion 𝔪) * rayClassIdealMainTerm 𝔪 =
      (unitsCongruenceSubgroupSupTorsion 𝔪).index *
          (2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K) /
        (2 ^ 𝔪.infinitePart.card * Ideal.absNorm 𝔪.finitePart * √|(discr K : ℝ)|) := by
  have h𝔪 : (Ideal.absNorm 𝔪.finitePart : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr 𝔪.finitePart_ne_zero)
  have := 𝔪.finitePart.finiteQuotientOfFreeOfNeBot 𝔪.finitePart_ne_bot
  -- the correction product is the proportion of residues modulo `𝔪₀` that are units
  rw [rayClassIdealMainTerm_eq, ← mul_div_cancel_left₀ (∏ v ∈ 𝔪.support, _) h𝔪,
    ← Ideal.card_units_quotient_eq_absNorm_mul_prod 𝔪.finitePart 𝔪.mem_support_iff,
    dedekindZeta_residue_def, classNumber, ← Nat.card_eq_fintype_card]
  field_simp [discr_ne_zero, torsionOrder_ne_zero, Nat.card_pos.ne']
  -- `h_𝔪 · [E : E_𝔪] = h · #(𝓞 K ⧸ 𝔪₀)ˣ · 2 ^ s` and `[E : E_𝔪] · w_𝔪 = [E : E_𝔪 μ_K] · w_K`
  grind [congrArg (Nat.cast : ℕ → ℝ) (card_rayClassGroup_mul_index 𝔪),
    congrArg (Nat.cast : ℕ → ℝ) (index_unitsCongruenceSubgroup_mul_card_unitsCongruenceTorsion 𝔪)]

open scoped Classical in
/-- **The geometric coefficient of the ray ideal count.**  The volume of the norm-one section of
`rayFundamentalDomain 𝔪`, over the covolume of the congruence lattice of a nonzero integral ideal
`𝔞`, times the norm of `𝔞`, is `w_𝔪 · rayClassIdealMainTerm 𝔪`, where `w_𝔪` is the number of
roots of unity congruent to one modulo `𝔪`. In particular the left-hand side does not depend
on `𝔞`. -/
theorem measureReal_div_covolume_congruenceLattice_mul_absNorm (𝔪 : Modulus K)
    (𝔞 : (Ideal (𝓞 K))⁰) :
    volume.real (rayFundamentalDomain 𝔪 ∩ {x | mixedEmbedding.norm x ≤ 1}) /
          ZLattice.covolume (congruenceLattice 𝔪 (FractionalIdeal.mk0 K 𝔞)) volume *
        Ideal.absNorm (𝔞 : Ideal (𝓞 K)) =
      Nat.card (unitsCongruenceTorsion 𝔪) * rayClassIdealMainTerm 𝔪 := by
  have h := covolume_congruenceLattice_div_absNorm 𝔪 (FractionalIdeal.mk0 K 𝔞)
  rw [FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast] at h
  rw [div_mul_eq_mul_div, ← div_div_eq_mul_div, h,
    measureReal_rayFundamentalDomain_inter_normLeOne,
    card_unitsCongruenceTorsion_mul_rayClassIdealMainTerm]
  field_simp
  ring

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
# The ray class count, reindexed by a representative ideal

Counting the integral ideals of a fixed ray class is awkward directly, because the class
condition is not a divisibility condition.  Multiplying by an ideal `𝔞` whose class is the
inverse one turns it into two conditions that are: divisibility by `𝔞`, and triviality of the
class.  The norm bound is carried along, scaled by the norm of `𝔞`.

## Main results

* `TauCeti.GlobalNumberFields.rayClassIdealCountingFunction_eq_card_dvd_and_idealClass_eq_one`:
  the counting function as the number of multiples of `𝔞` of trivial class and bounded norm.

## Provenance

The reindexing follows Mathlib's class-group analogue
`NumberField.Ideal.tendsto_norm_le_and_mk_eq_div_atTop_aux₁`
(`Mathlib/NumberTheory/NumberField/Ideal/Asymptotics.lean`) move for move: `subtypeEquiv`, then
`subtypeSubtypeEquivSubtypeInter`, then `Nat.card_congr`.  That lemma is `private`, is a
`Nat.card` equality rather than an `Equiv`, and is stated over `(Ideal (𝓞 K))⁰`, so it cannot be
called from here.
-/

 section

open NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- **The ray class count, reindexed by a representative.**  For `𝔞` in the inverse class of `c`,
multiplication by `𝔞` matches the ideals of class `c` with norm at most `x` against the multiples
of `𝔞` of trivial class with norm at most `x * N 𝔞`. -/
private noncomputable def idealClassNormLEEquivDvdIdealClassOneNormLE (𝔪 : Modulus K)
    {c : RayClassGroup 𝔪}
    (𝔞 : integralIdealsPrimeTo 𝔪) (h𝔞 : idealClass 𝔪 𝔞 = c⁻¹) (x : ℝ) :
    {I : integralIdealsPrimeTo 𝔪 // idealClass 𝔪 I = c ∧
      (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x} ≃
      {I : integralIdealsPrimeTo 𝔪 // 𝔞 ∣ I ∧ idealClass 𝔪 I = 1 ∧
        (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x * Ideal.absNorm (𝔞 : Ideal (𝓞 K))} :=
  ((Equiv.dvd 𝔞).subtypeEquiv fun I ↦ by
    simp only [Equiv.dvd_apply, Submonoid.coe_mul, map_mul, h𝔞, Nat.cast_mul,
      inv_mul_eq_one, mul_comm x]
    -- `N 𝔞` is nonzero, so it cancels from the scaled norm bound
    exact and_congr eq_comm (mul_le_mul_iff_of_pos_left (Nat.cast_pos.mpr (Nat.pos_of_ne_zero
      (mt Ideal.absNorm_eq_zero_iff.mp
        (NumberFieldArithmetic.mem_integralIdealsAway_iff.mp 𝔞.prop).1)))).symm).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun I : integralIdealsPrimeTo 𝔪 ↦ 𝔞 ∣ I) _)

/-- **The counting function as a count of multiples of `𝔞`.**  For `𝔞` in the inverse class of
`c`, the count runs over the multiples of `𝔞` of trivial class, against a norm bound scaled by
`N 𝔞`; any `𝔞` of that class serves, as the left-hand side does not mention it.  This is the
rewrite that trades the class condition for a divisibility condition, where
`rayClassIdealCountingFunction_def` is the one that keeps the class condition. -/
theorem rayClassIdealCountingFunction_eq_card_dvd_and_idealClass_eq_one (𝔪 : Modulus K)
    {c : RayClassGroup 𝔪} (𝔞 : integralIdealsPrimeTo 𝔪) (h𝔞 : idealClass 𝔪 𝔞 = c⁻¹) (x : ℝ) :
    rayClassIdealCountingFunction 𝔪 c x = Nat.card {I : integralIdealsPrimeTo 𝔪 // 𝔞 ∣ I ∧
      idealClass 𝔪 I = 1 ∧ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤
        x * Ideal.absNorm (𝔞 : Ideal (𝓞 K))} :=
  -- `rayClassIdealCountingFunction` is not `@[expose]`d, so the step onto the cardinality it is
  -- defined as goes through `rayClassIdealCountingFunction_def` rather than by `rfl`
  (rayClassIdealCountingFunction_def 𝔪 c x).trans <|
    Nat.card_congr <| idealClassNormLEEquivDvdIdealClassOneNormLE 𝔪 𝔞 h𝔞 x

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
# The asymptotic count of the integral ideals of a ray class

Let `𝔪` be a modulus of a number field `K` of degree `n`.  This file proves that the number of
nonzero integral ideals prime to `𝔪` in a fixed ray class with absolute norm at most `x` is
`rayClassIdealMainTerm 𝔪 * x + O(x ^ (1 - 1 / n))`, with the same main term and the same power
saving for every class.

## Main results

* `TauCeti.GlobalNumberFields.isBigO_rayClassIdealCountingFunction_sub`: the ray class ideal
  counting function of a class is `rayClassIdealMainTerm 𝔪 * x + O(x ^ (1 - 1 / [K : ℚ]))`.
* `TauCeti.GlobalNumberFields.rayClassIdealCount`: the ray class ideal counting function is
  `rayClassIdealMainTerm 𝔪 * x + O(x ^ (1 - δ))` for some `δ > 0` uniform in the class.
-/

 section

open Asymptotics Filter MeasureTheory Module NumberField NumberField.mixedEmbedding
open scoped nonZeroDivisors Pointwise

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

private theorem rayClassIdealCountingFunction_mul_card_eq_ncard (𝔪 : Modulus K)
    {c : RayClassGroup 𝔪} (𝔞 : integralIdealsPrimeTo 𝔪) (h𝔞 : idealClass 𝔪 𝔞 = c⁻¹)
    (h𝔞0 : (𝔞 : Ideal (𝓞 K)) ∈ (Ideal (𝓞 K))⁰) {ξ : 𝓞 K} (hξ𝔞 : ξ ∈ (𝔞 : Ideal (𝓞 K)))
    (hξ𝔪 : ξ - 1 ∈ 𝔪.finitePart) (x : ℝ) :
    rayClassIdealCountingFunction 𝔪 c x * Nat.card (unitsCongruenceTorsion 𝔪) =
      ((rayFundamentalDomain 𝔪 ∩
          {y | mixedEmbedding.norm y ≤ x * Ideal.absNorm (𝔞 : Ideal (𝓞 K))}) ∩
        (mixedEmbedding K (ξ : K) +ᵥ
          (congruenceLattice 𝔪 (FractionalIdeal.mk0 K ⟨𝔞, h𝔞0⟩) : Set (mixedSpace K)))).ncard := by
  -- as `𝔞` lies in the inverse class and `ξ ∈ 𝔞` is congruent to one modulo `𝔪₀`, the ideals of
  -- `c` of norm at most `x`, counted with the roots of unity congruent to one modulo `𝔪`, match
  -- the points of norm at most `x · N𝔞` of the coset `ξ + Λ` of the congruence lattice of `𝔞`
  -- in the ray fundamental domain
  rw [rayClassIdealCountingFunction_eq_card_dvd_and_idealClass_eq_one 𝔪 𝔞 h𝔞 x,
    card_idealClass_eq_one_dvd_norm_le, ← Nat.card_coe_set_eq, Set.inter_right_comm,
    ← rayIdealSet_eq_inter_vadd 𝔪 ⟨𝔞, h𝔞0⟩ hξ𝔞 hξ𝔪]
  exact Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter _ (mixedEmbedding.norm · ≤ _))

private theorem exists_mem_idealClass_inv_and_sub_one_mem (𝔪 : Modulus K) (c : RayClassGroup 𝔪) :
    ∃ 𝔞 : integralIdealsPrimeTo 𝔪, idealClass 𝔪 𝔞 = c⁻¹ ∧
      (𝔞 : Ideal (𝓞 K)) ∈ (Ideal (𝓞 K))⁰ ∧ ∃ ξ ∈ (𝔞 : Ideal (𝓞 K)), ξ - 1 ∈ 𝔪.finitePart := by
  obtain ⟨𝔞, h𝔞⟩ := idealClass_surjective 𝔪 c⁻¹
  refine ⟨𝔞, h𝔞, mem_nonZeroDivisors_of_ne_zero
    (NumberFieldArithmetic.mem_integralIdealsAway_iff.mp 𝔞.prop).1, ?_⟩
  -- `𝔞` is coprime to `𝔪₀`, so it contains an element congruent to one modulo `𝔪₀`
  exact Ideal.isCoprime_iff_exists_mem_and_sub_one_mem.mp <| Ideal.isCoprime_iff_sup_eq.mpr
    (Modulus.isCoprimeTo_iff_sup_eq_top.mp (Modulus.mem_integralIdealsPrimeTo.mp 𝔞.prop)).2

private theorem exists_abs_rayClassIdealCountingFunction_sub_le (𝔪 : Modulus K)
    {c : RayClassGroup 𝔪} (𝔞 : integralIdealsPrimeTo 𝔪) (h𝔞 : idealClass 𝔪 𝔞 = c⁻¹)
    (h𝔞0 : (𝔞 : Ideal (𝓞 K)) ∈ (Ideal (𝓞 K))⁰) {ξ : 𝓞 K} (hξ𝔞 : ξ ∈ (𝔞 : Ideal (𝓞 K)))
    (hξ𝔪 : ξ - 1 ∈ 𝔪.finitePart) : ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      |(rayClassIdealCountingFunction 𝔪 c x : ℝ) - rayClassIdealMainTerm 𝔪 * x| ≤
        C * x ^ (1 - (finrank ℚ K : ℝ)⁻¹) := by
  obtain ⟨A, -, hA⟩ := exists_abs_ncard_rayFundamentalDomain_inter_norm_le_inter_vadd_sub_le 𝔪
    (FractionalIdeal.mk0 K ⟨𝔞, h𝔞0⟩)
  set N : ℝ := (Ideal.absNorm (𝔞 : Ideal (𝓞 K)) : ℝ)
  have hN : 1 ≤ N := Nat.one_le_cast.mpr (Ideal.absNorm_pos_of_nonZeroDivisors ⟨_, h𝔞0⟩)
  have hw : 0 < (Nat.card (unitsCongruenceTorsion 𝔪) : ℝ) := Nat.cast_pos.mpr Nat.card_pos
  refine ⟨A * N ^ (1 - (finrank ℚ K : ℝ)⁻¹) / Nat.card (unitsCongruenceTorsion 𝔪), fun x hx ↦ ?_⟩
  have hcount := hA (mixedEmbedding K (ξ : K)) (x * N) (one_le_mul_of_one_le_of_one_le hx hN)
  -- the lattice-point count is `w` times the ideal count, and its main term `w` times ours,
  -- where `w` is the number of roots of unity congruent to one modulo `𝔪`
  rw [← rayClassIdealCountingFunction_mul_card_eq_ncard 𝔪 𝔞 h𝔞 _ hξ𝔞 hξ𝔪 x, Nat.cast_mul,
    mul_left_comm _ x, measureReal_div_covolume_congruenceLattice_mul_absNorm 𝔪 ⟨𝔞, h𝔞0⟩,
    Real.mul_rpow (zero_le_one.trans hx) (zero_le_one.trans hN)] at hcount
  rw [div_mul_eq_mul_div, le_div_iff₀ hw, ← abs_of_pos hw, ← abs_mul]
  refine le_of_eq_of_le ?_ (hcount.trans_eq ?_)
  · ring_nf
  · ring

/-- **The ray class ideal count of a single class, with an explicit power saving.**  The number
of nonzero integral ideals prime to `𝔪` in the ray class `c` with norm at most `x` is
`rayClassIdealMainTerm 𝔪 * x + O(x ^ (1 - 1 / [K : ℚ]))`. -/
theorem isBigO_rayClassIdealCountingFunction_sub (𝔪 : Modulus K) (c : RayClassGroup 𝔪) :
    (fun x : ℝ => (rayClassIdealCountingFunction 𝔪 c x : ℝ) - rayClassIdealMainTerm 𝔪 * x) =O[atTop]
      fun x : ℝ => x ^ (1 - (finrank ℚ K : ℝ)⁻¹) := by
  -- an ideal `𝔞` of the inverse class and an element of `𝔞` congruent to one modulo `𝔪₀` place
  -- the counted points in one coset of a congruence lattice
  obtain ⟨𝔞, h𝔞, h𝔞0, ξ, hξ𝔞, hξ𝔪⟩ := exists_mem_idealClass_inv_and_sub_one_mem 𝔪 c
  obtain ⟨C, hC⟩ := exists_abs_rayClassIdealCountingFunction_sub_le 𝔪 𝔞 h𝔞 h𝔞0 hξ𝔞 hξ𝔪
  refine IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hx) _)]
  exact hC x hx



end TauCeti.GlobalNumberFields

end
end

section
set_option autoImplicit true
namespace TauCeti.GlobalNumberFields
end TauCeti.GlobalNumberFields
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The Dedekind zeta function across the line `Re s = 1`

Let `K` be a number field of degree `d = [K : ℚ]`. The number of nonzero integral ideals of `𝓞 K`
of absolute norm at most `x` is `ρ x + O(x ^ (1 - 1 / d))`, where `ρ = dedekindZeta_residue K`:
summing the ray class ideal counts over the classes of the trivial modulus recovers the total
count, and every class has the same main term.

By partial summation this power saving continues the Dedekind zeta function across the line
`Re s = 1`, with a single simple pole there. Comparing the Dirichlet coefficients of `ζ_K` with
`ρ` times those of the Riemann zeta function, the difference has partial sums `O(n ^ (1 - 1 / d))`,
so its `L`-series continues holomorphically to `Re s > 1 - 1 / d`; and `ζ(s) - 1 / (s - 1)` is
entire (Mathlib's `riemannZeta₀`). Hence `ζ_K(s) - ρ / (s - 1)` agrees on `Re s > 1` with a
function holomorphic on `Re s > 1 - 1 / d`.

Deleting finitely many Euler factors multiplies `ζ_K` by the entire function
`∏ 𝔭 ∈ S, (1 - N(𝔭) ^ (-s))`, so the Dedekind zeta function with the Euler factors at a finite set
`S` of primes deleted has the same kind of continuation, with residue
`ρ * ∏ 𝔭 ∈ S, (1 - N(𝔭) ^ (-1))` at its simple pole `s = 1`. This is the `L`-series of the trivial
member of a family of ideal weights with bad primes `S`, such as the trivial Galois character of a
Galois extension, whose bad primes are the ramified ones.

## Main results

* `TauCeti.setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re`: the closed half-plane
  `Re s ≥ 1` lies in the half-plane of continuation.
* `TauCeti.isBigO_card_idealsLE_sub`: the number of nonzero integral ideals of norm at most `x` is
  `ρ x + O(x ^ (1 - 1 / [K : ℚ]))`.
* `TauCeti.exists_differentiableOn_eq_dedekindZeta_sub`: `ζ_K(s) - ρ / (s - 1)` extends
  holomorphically from `Re s > 1` to `Re s > 1 - 1 / [K : ℚ]`.
* `TauCeti.exists_differentiableOn_eq_LSeries_ofBadPrimes_sub`: the same for the Dedekind zeta
  function with the Euler factors at a finite set of primes deleted, with the correspondingly
  corrected residue.

## References

* S. Lang, *Algebraic Number Theory*, Chapter VI and Chapter VIII, §3.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter II.1.
-/

 section

open _root_.Asymptotics _root_.Filter _root_.IsDedekindDomain _root_.NumberField _root_.TauCeti.GlobalNumberFields
open scoped _root_.nonZeroDivisors

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti



variable (K : Type*) [Field K] [NumberField K]

-- The nonzero integral ideals of norm at most `x` are those prime to the trivial modulus.
private theorem TauCeti.card_idealsLE_eq_sum_rayClassIdealCountingFunction
    [_root_.Fintype (_root_.TauCeti.GlobalNumberFields.RayClassGroup (_root_.TauCeti.GlobalNumberFields.Modulus.one K))] (x : ℝ) :
    (_root_.TauCeti.idealsLE K x).card =
      ∑ c : _root_.TauCeti.GlobalNumberFields.RayClassGroup (_root_.TauCeti.GlobalNumberFields.Modulus.one K), _root_.TauCeti.GlobalNumberFields.rayClassIdealCountingFunction (_root_.TauCeti.GlobalNumberFields.Modulus.one K) c x := by
  rw [_root_.TauCeti.GlobalNumberFields.sum_rayClassIdealCountingFunction, ← _root_.Nat.card_eq_finsetCard]
  -- An ideal is prime to the trivial modulus exactly when it is nonzero.
  have hmem (I : _root_.Ideal (𝓞 K)) :
      I ∈ (_root_.Ideal (𝓞 K))⁰ ↔ I ∈ _root_.TauCeti.GlobalNumberFields.integralIdealsPrimeTo (_root_.TauCeti.GlobalNumberFields.Modulus.one K) := by
    simp [_root_.mem_nonZeroDivisors_iff_ne_zero, _root_.TauCeti.NumberFieldArithmetic.mem_integralIdealsAway_iff]
  exact _root_.Nat.card_congr <| _root_.Equiv.subtypeEquiv (_root_.Equiv.subtypeEquivRight hmem) fun _ ↦ _root_.TauCeti.mem_normLE _

/-- **The ideal count with a power saving.** The number of nonzero integral ideals of `𝓞 K` of
absolute norm at most `x` is `dedekindZeta_residue K * x + O(x ^ (1 - 1 / [K : ℚ]))`. -/
theorem solution :
    (fun x : ℝ ↦ ((_root_.TauCeti.idealsLE K x).card : ℝ) - _root_.NumberField.dedekindZeta_residue K * x) =O[_root_.Filter.atTop]
      fun x : ℝ ↦ x ^ (1 - (_root_.Module.finrank ℚ K : ℝ)⁻¹) := by
  have : _root_.Fintype (_root_.TauCeti.GlobalNumberFields.RayClassGroup (_root_.TauCeti.GlobalNumberFields.Modulus.one K)) := _root_.Fintype.ofFinite _
  -- Each of the `#Cl(K)` classes of the trivial modulus has main term `ρ / #Cl(K)`.
  have hmain : ∑ _c : _root_.TauCeti.GlobalNumberFields.RayClassGroup (_root_.TauCeti.GlobalNumberFields.Modulus.one K), _root_.TauCeti.GlobalNumberFields.rayClassIdealMainTerm (_root_.TauCeti.GlobalNumberFields.Modulus.one K) =
      _root_.NumberField.dedekindZeta_residue K := by
    rw [_root_.Finset.sum_const, _root_.Finset.card_univ, ← _root_.Nat.card_eq_fintype_card, _root_.nsmul_eq_mul,
      _root_.TauCeti.GlobalNumberFields.rayClassIdealMainTerm_eq, _root_.TauCeti.GlobalNumberFields.Modulus.support_one, _root_.Finset.prod_empty, _root_.mul_one,
      _root_.mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr Nat.card_pos.ne')]
  have heq (x : ℝ) : ((_root_.TauCeti.idealsLE K x).card : ℝ) - _root_.NumberField.dedekindZeta_residue K * x =
      ∑ c : _root_.TauCeti.GlobalNumberFields.RayClassGroup (_root_.TauCeti.GlobalNumberFields.Modulus.one K),
        ((_root_.TauCeti.GlobalNumberFields.rayClassIdealCountingFunction (_root_.TauCeti.GlobalNumberFields.Modulus.one K) c x : ℝ) -
          _root_.TauCeti.GlobalNumberFields.rayClassIdealMainTerm (_root_.TauCeti.GlobalNumberFields.Modulus.one K) * x) := by
    rw [_root_.Finset.sum_sub_distrib, ← _root_.Finset.sum_mul, hmain,
      _root_.TauCeti.card_idealsLE_eq_sum_rayClassIdealCountingFunction, _root_.Nat.cast_sum]
  simp_rw [heq]
  exact _root_.Asymptotics.IsBigO.fun_sum fun c _ ↦ _root_.TauCeti.GlobalNumberFields.isBigO_rayClassIdealCountingFunction_sub (_root_.TauCeti.GlobalNumberFields.Modulus.one K) c

-- The Dirichlet coefficients of `ζ_K` minus `ρ` times those of the Riemann zeta function have
-- partial sums `O(n ^ (1 - 1 / [K : ℚ]))`.






end TauCeti

end
end
