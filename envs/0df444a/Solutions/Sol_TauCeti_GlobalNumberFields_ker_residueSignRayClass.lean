-- Prove2me | solution 1 for TauCeti.GlobalNumberFields.ker_residueSignRayClass
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:16:52.526479+00:00
-- url     : https://prove2.me/submissions/a8cc0e5b-c8b5-4641-8903-db5b6babb65f

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_Algebra_Order_Ring_Units
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_Approximation_Weak
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Basic
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_CongruenceQuotient
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Exact
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Modulus
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Residue
import Definitions.Def_TauCeti_NumberTheory_NumberField_Ideal_Away
import Definitions.Def_TauCeti_NumberTheory_NumberField_SignApproximation
import Definitions.Def_TauCeti_NumberTheory_NumberField_Units_Signature_Basic
import Definitions.Def_TauCeti_NumberTheory_NumberField_Units_Signature_Integer
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Factorization
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Ideal
import Definitions.Def_TauCeti_RingTheory_Ideal_Quotient_Representative
import Definitions.Def_TauCeti_RingTheory_Valuation_AbsoluteValue
import Definitions.Def_TauCeti_RingTheory_Valuation_Approximation
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Algebra.Order.Ring.Units
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Data.Int.WithZero
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
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
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Group

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
# Complements on the ideal class group

Four facts about Mathlib's `ClassGroup R` and its principal-ideal map that Mathlib's own file does
not carry: the kernel of `toPrincipalIdeal`, the generator form of triviality of a class, that a
principal fractional ideal has trivial class, and the class `[v]` of a height one prime.

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.classGroupMk`: the class `[v]` of a height one prime of a
  Dedekind domain.

## Main results

* `FractionalIdeal.toPrincipalIdeal_eq_one_iff`: the kernel of the principal-ideal homomorphism is
  the image of `Rˣ`, that is, `(u)` is trivial exactly when `u` comes from a unit of `R`. This is
  the left end of the ideal class exact sequence. The underlying computation is Mathlib's
  `Submodule.span_singleton_eq_one_iff`, reached by coercing the fractional ideal to a submodule.
* `ClassGroup.mk_eq_one_iff_exists`: a class is trivial exactly when some `x : Kˣ` generates it.
  This is Mathlib's `ClassGroup.mk_eq_one_iff` with `Submodule.IsPrincipal` traded for the range
  of `toPrincipalIdeal`, which is the form a consumer that wants to *name* the generator can use.
* `ClassGroup.mk_toPrincipalIdeal`: a principal fractional ideal has trivial class. This is the
  `simp` form of `ClassGroup.mk_eq_one_iff` for the one witness that arises in practice, and it
  holds over any domain.
* `IsDedekindDomain.HeightOneSpectrum.classGroupMk_eq_mk0`: the defining formula for `[v]`, as
  `ClassGroup.mk0` of `v.asIdeal`. This needs no fraction field.
* `IsDedekindDomain.HeightOneSpectrum.classGroupMk_eq_mk`: `[v]` is the class of `v.asIdeal` seen
  as an invertible fractional ideal of any fraction field `K`.

All are stated at the weakest hypotheses their proofs need: the two class-triviality results over
`[IsDomain R]`, since nothing in either is Dedekind-specific, and `toPrincipalIdeal_eq_one_iff`
over a plain `[CommRing R]`, since routing it through Mathlib's submodule lemma needs no domain
hypothesis at all. None
of them needs the factorization of a fractional ideal into primes, so this file does not import
it; the results that do live in
`TauCeti.RingTheory.ClassGroup.HeightOneSpectrum`, which every consumer of *those* pays for and
consumers of these do not.

Split out of material adapted from Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/FractionalIdeal.lean`
at the roadmap's pin `66889eada51a`, Apache 2.0, by Michael Stoll). Following this repository's
convention for adapted material, the upstream authorship is credited here rather than in the
copyright header.
-/

 section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors

/-- The kernel of the principal-ideal map is the image of `Rˣ`: `toPrincipalIdeal R K u` is trivial
exactly when `u` comes from a unit of `R`. This is the left end of the ideal class exact
sequence. -/
lemma FractionalIdeal.toPrincipalIdeal_eq_one_iff {R : Type*} [CommRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (u : Kˣ) :
    toPrincipalIdeal R K u = 1 ↔ ∃ a : Rˣ, Units.map (algebraMap R K : R →* K) a = u := by
  rw [← Units.val_inj, coe_toPrincipalIdeal, Units.val_one, ← coeToSubmodule_inj,
    coe_spanSingleton, coe_one, Submodule.span_singleton_eq_one_iff]
  exact ⟨fun ⟨a, ha⟩ ↦ ⟨a, Units.ext ha.symm⟩, fun ⟨a, ha⟩ ↦ ⟨a, by rw [← ha]; rfl⟩⟩





variable {R : Type*} [CommRing R] [IsDedekindDomain R]



-- Deliberately not `@[simp]`: the statements that matter here are phrased in the folded form,
-- and in `HeightOneSpectrum.classGroupMk '' T` the occurrence is unapplied, so `simp` could not
-- unfold it there anyway — tagging this would only leave goals in mixed normal forms.




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
end TauCeti.GlobalNumberFields
section TauCeti.GlobalNumberFields
open TauCeti TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]





















/-! ### The residue-and-sign presentation of the exact sequence -/

/-- **A principal ray class is trivial exactly when a unit multiple of the generator is congruent
to one.**  Two generators of the same principal fractional ideal differ by a unit of `𝓞 K`, so the
ray only sees an element of `primeToSubgroup 𝔪` up to the integer units. -/
theorem TauCeti.GlobalNumberFields.principalRayClass_eq_one_iff {𝔪 : _root_.TauCeti.GlobalNumberFields.Modulus K} (x : _root_.TauCeti.GlobalNumberFields.primeToSubgroup 𝔪) :
    _root_.TauCeti.GlobalNumberFields.principalRayClass 𝔪 x = 1 ↔
      ∃ u : (𝓞 K)ˣ, _root_.TauCeti.GlobalNumberFields.IsCongrOne 𝔪 (_root_.Units.map (_root_.Algebra.algebraMap (𝓞 K) K).toMonoidHom u * x) := by
  rw [_root_.TauCeti.GlobalNumberFields.principalRayClass_apply, _root_.TauCeti.GlobalNumberFields.rayClassMk_eq_one_iff, _root_.TauCeti.GlobalNumberFields.mem_ray_iff, _root_.TauCeti.GlobalNumberFields.coe_principalIdealPrimeTo]
  refine ⟨fun ⟨y, hy, hyx⟩ ↦ ?_, fun ⟨u, hu⟩ ↦ ⟨_, hu, ?_⟩⟩
  · obtain ⟨u, hu⟩ := (_root_.FractionalIdeal.toPrincipalIdeal_eq_one_iff (y * (x : Kˣ)⁻¹)).mp
      (by rw [_root_.map_mul, _root_.map_inv, hyx, _root_.mul_inv_cancel])
    refine ⟨u, ?_⟩
    have hu' : _root_.Units.map (_root_.Algebra.algebraMap (𝓞 K) K).toMonoidHom u = y * (x : Kˣ)⁻¹ := hu
    rwa [hu', _root_.inv_mul_cancel_right]
  · have hu1 : _root_.toPrincipalIdeal (𝓞 K) K (_root_.Units.map (_root_.Algebra.algebraMap (𝓞 K) K).toMonoidHom u) = 1 :=
      (_root_.FractionalIdeal.toPrincipalIdeal_eq_one_iff _).mpr ⟨u, _root_.rfl⟩
    rw [_root_.map_mul, hu1, _root_.one_mul]



@[simp] theorem TauCeti.GlobalNumberFields.unitsResidueSignHom_apply (𝔪 : _root_.TauCeti.GlobalNumberFields.Modulus K) (u : (𝓞 K)ˣ) :
    _root_.TauCeti.GlobalNumberFields.unitsResidueSignHom 𝔪 u = _root_.TauCeti.GlobalNumberFields.residueSignHom 𝔪 (_root_.TauCeti.GlobalNumberFields.unitsToPrimeToSubgroup 𝔪 u) := (_root_.rfl)







/-- The class attached to the residue and signs of an element is its principal ray class. -/
@[simp] theorem TauCeti.GlobalNumberFields.residueSignRayClass_residueSignHom (𝔪 : _root_.TauCeti.GlobalNumberFields.Modulus K) (x : _root_.TauCeti.GlobalNumberFields.primeToSubgroup 𝔪) :
    _root_.TauCeti.GlobalNumberFields.residueSignRayClass 𝔪 (_root_.TauCeti.GlobalNumberFields.residueSignHom 𝔪 x) = _root_.TauCeti.GlobalNumberFields.principalRayClass 𝔪 x := by
  rw [_root_.TauCeti.GlobalNumberFields.residueSignRayClass, _root_.MonoidHom.comp_apply, _root_.MulEquiv.coe_toMonoidHom,
    (_root_.TauCeti.GlobalNumberFields.residueSignEquiv 𝔪).symm_apply_eq.mpr (_root_.TauCeti.GlobalNumberFields.residueSignEquiv_apply_mk 𝔪 x).symm,
    _root_.QuotientGroup.lift_mk]



/-- **Exactness at the residue units and signs**: a residue unit and sign pattern has trivial ray
class exactly when it is the residue and sign pattern of an integer unit. -/
theorem solution (𝔪 : _root_.TauCeti.GlobalNumberFields.Modulus K) :
    (_root_.TauCeti.GlobalNumberFields.residueSignRayClass 𝔪).ker = (_root_.TauCeti.GlobalNumberFields.unitsResidueSignHom 𝔪).range := by
  ext a
  obtain ⟨x, rfl⟩ := _root_.TauCeti.GlobalNumberFields.residueSignHom_surjective 𝔪 a
  rw [_root_.MonoidHom.mem_ker, _root_.TauCeti.GlobalNumberFields.residueSignRayClass_residueSignHom, _root_.TauCeti.GlobalNumberFields.principalRayClass_eq_one_iff,
    _root_.MonoidHom.mem_range]
  refine ⟨fun ⟨u, hu⟩ ↦ ⟨u⁻¹, ?_⟩, fun ⟨u, hu⟩ ↦ ⟨u⁻¹, ?_⟩⟩
  · have h := (_root_.TauCeti.GlobalNumberFields.residueSignHom_eq_one_iff (_root_.TauCeti.GlobalNumberFields.unitsToPrimeToSubgroup 𝔪 u * x)).mpr
      (by rwa [_root_.Subgroup.coe_mul, _root_.TauCeti.GlobalNumberFields.coe_unitsToPrimeToSubgroup, _root_.TauCeti.GlobalNumberFields.mem_congruenceSubgroup])
    rw [_root_.map_mul] at h
    rw [_root_.TauCeti.GlobalNumberFields.unitsResidueSignHom_apply, _root_.map_inv, _root_.map_inv, _root_.inv_eq_of_mul_eq_one_right h]
  · have h : _root_.TauCeti.GlobalNumberFields.residueSignHom 𝔪 (_root_.TauCeti.GlobalNumberFields.unitsToPrimeToSubgroup 𝔪 u⁻¹ * x) = 1 := by
      rw [_root_.map_mul, _root_.map_inv, _root_.map_inv, ← _root_.TauCeti.GlobalNumberFields.unitsResidueSignHom_apply, hu, _root_.inv_mul_cancel]
    rwa [_root_.TauCeti.GlobalNumberFields.residueSignHom_eq_one_iff, _root_.Subgroup.coe_mul, _root_.TauCeti.GlobalNumberFields.coe_unitsToPrimeToSubgroup,
      _root_.TauCeti.GlobalNumberFields.mem_congruenceSubgroup] at h







end TauCeti.GlobalNumberFields

end
end
