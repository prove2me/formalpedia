-- Prove2me | solution 1 for TauCeti.GlobalNumberFields.unitsCongruenceSubgroup_smul_mem_rayFundamentalDomain_iff_mem_torsion
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:16:57.292504+00:00
-- url     : https://prove2.me/submissions/4a2f0f6e-90a6-4923-b7d0-4beaf8def918

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_NumberField_CanonicalEmbedding_UnitAction
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_Counting_RayFundamentalDomain_Basic
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Modulus
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Order.Ring.Units
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Defs
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
end TauCeti.GlobalNumberFields
section TauCeti.GlobalNumberFields
open TauCeti TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-! ### The congruence units and the roots of unity -/







/-- The roots of unity lie in `unitsCongruenceSubgroupSupTorsion 𝔪`. -/
theorem TauCeti.GlobalNumberFields.torsion_le_unitsCongruenceSubgroupSupTorsion (𝔪 : _root_.TauCeti.GlobalNumberFields.Modulus K) :
    _root_.NumberField.Units.torsion K ≤ _root_.TauCeti.GlobalNumberFields.unitsCongruenceSubgroupSupTorsion 𝔪 :=
  _root_.le_sup_right









/-! ### The sign conditions prescribed by the infinite part -/



















/-! ### The fundamental domain -/









































/-- **Uniqueness of the representative, modulo roots of unity.** A unit congruent to one modulo
`𝔪` carries a point of the ray fundamental domain back into the ray fundamental domain exactly
when it is a root of unity.

Together with `exists_unitsCongruenceSubgroup_smul_mem_rayFundamentalDomain` this says that the
domain meets each orbit of nonzero mixed norm of the congruence units inside `posRegion 𝔪` in
one point, modulo the congruence units that are roots of unity: the sense in which Mathlib's
fundamental cone is fundamental for the full unit group. -/
theorem solution {𝔪 : _root_.TauCeti.GlobalNumberFields.Modulus K}
    {x : _root_.NumberField.mixedEmbedding.mixedSpace K} (hx : x ∈ _root_.TauCeti.GlobalNumberFields.rayFundamentalDomain 𝔪) {u : (𝓞 K)ˣ}
    (hu : u ∈ _root_.TauCeti.GlobalNumberFields.unitsCongruenceSubgroup 𝔪) :
    u • x ∈ _root_.TauCeti.GlobalNumberFields.rayFundamentalDomain 𝔪 ↔ u ∈ _root_.NumberField.Units.torsion K := by
  obtain ⟨q, hq⟩ := (mem_rayFundamentalDomain_iff.mp hx).2
  refine ⟨fun h ↦ ?_, fun hut ↦ (_root_.TauCeti.GlobalNumberFields.torsion_smul_mem_rayFundamentalDomain_iff hut hu).mpr hx⟩
  obtain ⟨q', hq'⟩ := (mem_rayFundamentalDomain_iff.mp h).2
  have hsmul :
      ((_root_.TauCeti.GlobalNumberFields.rayUnitRepresentative 𝔪 q')⁻¹ * u * _root_.TauCeti.GlobalNumberFields.rayUnitRepresentative 𝔪 q) •
          ((_root_.TauCeti.GlobalNumberFields.rayUnitRepresentative 𝔪 q)⁻¹ • x) =
        (_root_.TauCeti.GlobalNumberFields.rayUnitRepresentative 𝔪 q')⁻¹ • (u • x) := by
    rw [← _root_.SemigroupAction.mul_smul, ← _root_.SemigroupAction.mul_smul]
    congr 1
    group
  rw [← hsmul] at hq'
  have htor : (_root_.TauCeti.GlobalNumberFields.rayUnitRepresentative 𝔪 q')⁻¹ * u * _root_.TauCeti.GlobalNumberFields.rayUnitRepresentative 𝔪 q ∈
      _root_.NumberField.Units.torsion K :=
    (_root_.NumberField.mixedEmbedding.fundamentalCone.unit_smul_mem_iff_mem_torsion hq _).mp hq'
  have hqq : q = q' := by
    rw [← _root_.TauCeti.GlobalNumberFields.rayUnitRepresentative_mk 𝔪 q, ← _root_.TauCeti.GlobalNumberFields.rayUnitRepresentative_mk 𝔪 q']
    refine QuotientGroup.eq.mpr ?_
    have hsplit : (_root_.TauCeti.GlobalNumberFields.rayUnitRepresentative 𝔪 q)⁻¹ * _root_.TauCeti.GlobalNumberFields.rayUnitRepresentative 𝔪 q'
        = ((_root_.TauCeti.GlobalNumberFields.rayUnitRepresentative 𝔪 q')⁻¹ * u * _root_.TauCeti.GlobalNumberFields.rayUnitRepresentative 𝔪 q)⁻¹ * u := by
      simp [_root_.mul_comm, _root_.mul_left_comm]
    rw [hsplit]
    exact _root_.MulMemClass.mul_mem (_root_.InvMemClass.inv_mem (_root_.TauCeti.GlobalNumberFields.torsion_le_unitsCongruenceSubgroupSupTorsion 𝔪 htor))
      (_root_.TauCeti.GlobalNumberFields.unitsCongruenceSubgroup_le_unitsCongruenceSubgroupSupTorsion 𝔪 hu)
  subst hqq
  have hconj : (_root_.TauCeti.GlobalNumberFields.rayUnitRepresentative 𝔪 q)⁻¹ * u * _root_.TauCeti.GlobalNumberFields.rayUnitRepresentative 𝔪 q = u := by
    simp [_root_.mul_comm, _root_.mul_left_comm]
  rwa [hconj] at htor



end TauCeti.GlobalNumberFields

end
end
