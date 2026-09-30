-- Prove2me | solution 1 for TauCeti.GlobalNumberFields.index_unitsCongruenceSubgroup_mul_card_unitsCongruenceTorsion
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:16:51.005464+00:00
-- url     : https://prove2.me/submissions/3b6dc829-106a-4af0-b0cc-e5b70c182297

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
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



/-- `unitsCongruenceSubgroupSupTorsion 𝔪` is the join of `unitsCongruenceSubgroup 𝔪` and the roots
of unity. -/
theorem TauCeti.GlobalNumberFields.unitsCongruenceSubgroupSupTorsion_def (𝔪 : _root_.TauCeti.GlobalNumberFields.Modulus K) :
    _root_.TauCeti.GlobalNumberFields.unitsCongruenceSubgroupSupTorsion 𝔪 =
      _root_.TauCeti.GlobalNumberFields.unitsCongruenceSubgroup 𝔪 ⊔ _root_.NumberField.Units.torsion K :=
  (_root_.rfl)













/-! ### The sign conditions prescribed by the infinite part -/



















/-! ### The fundamental domain -/

































/-- **The index of the congruence units, corrected by torsion.**  Adjoining the roots of unity to
the units congruent to one modulo `𝔪` divides their index by the index of
`unitsCongruenceTorsion 𝔪` in the roots of unity:
`[E : E_𝔪] · #(E_𝔪 ∩ μ_K) = [E : E_𝔪 · μ_K] · #μ_K`.

The identity is stated multiplicatively, so it holds in `ℕ` with no divisibility side
condition. -/
theorem solution (𝔪 : _root_.TauCeti.GlobalNumberFields.Modulus K) :
    (_root_.TauCeti.GlobalNumberFields.unitsCongruenceSubgroup 𝔪).index * _root_.Nat.card (_root_.TauCeti.GlobalNumberFields.unitsCongruenceTorsion 𝔪) =
      (_root_.TauCeti.GlobalNumberFields.unitsCongruenceSubgroupSupTorsion 𝔪).index * _root_.NumberField.Units.torsionOrder K := by
  -- `[E_𝔪 · μ_K : E_𝔪] = [μ_K : E_𝔪 ∩ μ_K]` by the second isomorphism theorem
  have hrel : (_root_.TauCeti.GlobalNumberFields.unitsCongruenceSubgroup 𝔪).relIndex (_root_.TauCeti.GlobalNumberFields.unitsCongruenceSubgroupSupTorsion 𝔪) =
      (_root_.TauCeti.GlobalNumberFields.unitsCongruenceTorsion 𝔪).relIndex (_root_.NumberField.Units.torsion K) := by
    rw [_root_.TauCeti.GlobalNumberFields.unitsCongruenceSubgroupSupTorsion_def, _root_.Subgroup.relIndex_sup_left,
      ← _root_.Subgroup.inf_relIndex_right]
    rfl
  -- `#μ_K = #(E_𝔪 ∩ μ_K) · [μ_K : E_𝔪 ∩ μ_K]`
  have hcard := _root_.Subgroup.relIndex_mul_relIndex ⊥ (_root_.TauCeti.GlobalNumberFields.unitsCongruenceTorsion 𝔪) _ _root_.bot_le _root_.inf_le_right
  rw [_root_.Subgroup.relIndex_bot_left, _root_.Subgroup.relIndex_bot_left] at hcard
  rw [_root_.NumberField.Units.torsionOrder, ← hcard, ← _root_.Subgroup.relIndex_mul_index
    (_root_.TauCeti.GlobalNumberFields.unitsCongruenceSubgroup_le_unitsCongruenceSubgroupSupTorsion 𝔪), hrel]
  ring











end TauCeti.GlobalNumberFields

end
end
