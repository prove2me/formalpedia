-- Prove2me | solution 1 for TauCeti.GlobalNumberFields.exists_abs_ncard_rayFundamentalDomain_inter_norm_le_inter_vadd_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:50:56.273281+00:00
-- url     : https://prove2.me/submissions/c42b45d4-a02e-4081-b735-6497341310da

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_Algebra_Order_Ring_Units
import Definitions.Def_TauCeti_GroupTheory_Index_Basic
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_Counting_CongruenceLattice
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_Counting_RayFundamentalDomain_Basic
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Finite
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Modulus
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Residue
import Definitions.Def_TauCeti_NumberTheory_NumberField_TotallyPositive
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Factorization
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Ideal
import Definitions.Def_TauCeti_Topology_MetricSpace_LipschitzParametrizable
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Algebra.Order.Ring.Units
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.FractionalIdeal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Group
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Theorems.Thm_TauCeti_GlobalNumberFields_isLipschitzParametrizable_frontier_rayFundamentalDomain
import Theorems.Thm_TauCeti_exists_abs_ncard_smul_inter_vadd_sub_le

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The action of units on the mixed space

This file provides basic compatibility and measurability lemmas for the action of number-field
units on the mixed space.

## Main results

* `TauCeti.NumberField.Units.unitSMul_comm`: two unit actions commute;
* `TauCeti.NumberField.Units.unitSMul_real_smul`: the unit action commutes with real
  scalar multiplication;
* `MeasurableConstSMul (𝓞 K)ˣ (mixedEmbedding.mixedSpace K)`: the action of a fixed unit is
  measurable, so Mathlib's `measurable_const_smul` applies;
* `TauCeti.NumberField.Units.eq_one_of_unitSMul_mixedEmbedding_eq`: a unit fixing the image of a
  nonzero element of `K` is the identity.

It also identifies the units of the mixed space itself:

* `TauCeti.NumberField.mixedEmbedding.isUnit_iff_norm_ne_zero`: a point of the mixed space is a
  unit exactly when its norm is nonzero.
-/

 section

open NumberField

namespace TauCeti.NumberField.Units

variable {K : Type*} [Field K]



/-- The unit action on the mixed space commutes with the real scalar action. -/
theorem unitSMul_real_smul (u : (𝓞 K)ˣ) (c : ℝ) (x : mixedEmbedding.mixedSpace K) :
    u • (c • x) = c • (u • x) := by
  simpa only [mixedEmbedding.unitSMul_smul] using
    mul_smul_comm c (mixedEmbedding K (u : K)) x





end TauCeti.NumberField.Units

open NumberField.mixedEmbedding

namespace TauCeti.NumberField.mixedEmbedding

variable {K : Type*} [Field K] [NumberField K]



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

















/-! ### The sign conditions prescribed by the infinite part -/













/-- The positivity region is stable under multiplication by a positive real scalar. -/
theorem smul_mem_posRegion {𝔪 : Modulus K} {x : mixedSpace K} (hx : x ∈ posRegion 𝔪)
    {c : ℝ} (hc : 0 < c) : c • x ∈ posRegion 𝔪 := by
  refine fun w hw ↦ ?_
  have hcoord : (c • x).1 w = c * x.1 w := by simp
  rw [hcoord]
  exact mul_pos hc (hx w hw)





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





/-- The ray fundamental domain is stable under multiplication by a positive real scalar. Negative
scalars are excluded because they may violate nonempty sign conditions prescribed by the infinite
part of `𝔪`. -/
theorem smul_mem_rayFundamentalDomain {𝔪 : Modulus K} {x : mixedSpace K}
    (hx : x ∈ rayFundamentalDomain 𝔪) {c : ℝ} (hc : 0 < c) :
    c • x ∈ rayFundamentalDomain 𝔪 := by
  obtain ⟨hpos, q, hq⟩ := mem_rayFundamentalDomain_iff.mp hx
  refine mem_rayFundamentalDomain_iff.mpr ⟨smul_mem_posRegion hpos hc, q, ?_⟩
  rw [unitSMul_real_smul]
  exact fundamentalCone.smul_mem_of_mem hq hc.ne'

/-- Multiplication by a positive real scalar preserves membership in the ray fundamental domain. -/
@[simp]
theorem smul_mem_rayFundamentalDomain_iff {𝔪 : Modulus K} {x : mixedSpace K}
    {c : ℝ} (hc : 0 < c) :
    c • x ∈ rayFundamentalDomain 𝔪 ↔ x ∈ rayFundamentalDomain 𝔪 := by
  refine ⟨fun h ↦ ?_, fun h ↦ smul_mem_rayFundamentalDomain h hc⟩
  simpa only [inv_smul_smul₀ hc.ne'] using smul_mem_rayFundamentalDomain h (inv_pos.mpr hc)

/-- **The norm grading is a dilation.**  Scaling by `c > 0` preserves the ray fundamental domain
and multiplies `mixedEmbedding.norm` by `c ^ [K:ℚ]`, so the dilate by `c` of the norm-≤-one
section is the norm-≤-`c ^ [K:ℚ]` section.

It converts between the two gradings: the lattice-point estimate is stated for dilates of a
fixed region, while ideals are counted by their absolute norm. -/
@[simp]
theorem smul_rayFundamentalDomain_inter_normLeOne (𝔪 : Modulus K) {c : ℝ} (hc : 0 < c) :
    c • (rayFundamentalDomain 𝔪 ∩ {x : mixedSpace K | mixedEmbedding.norm x ≤ 1}) =
      rayFundamentalDomain 𝔪 ∩
        {x : mixedSpace K | mixedEmbedding.norm x ≤ c ^ Module.finrank ℚ K} := by
  ext y
  simp [Set.mem_smul_set_iff_inv_smul_mem₀ hc.ne',
    smul_mem_rayFundamentalDomain_iff (inv_pos.mpr hc), mixedEmbedding.norm_smul,
    abs_of_pos (inv_pos.mpr hc), inv_mul_le_iff₀ (pow_pos hc _)]





















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

open scoped Classical in
/-- A unit translate of Mathlib's norm-≤-one region is bounded, because the unit acts by a
Lipschitz map. -/
private theorem isBounded_unitSMul_normLeOne (u : (𝓞 K)ˣ) :
    Bornology.IsBounded (u • normLeOne K) := by
  -- the unit action *is* multiplication by `mixedEmbedding K u`, so Mathlib's bound applies
  have hC : LipschitzWith ‖mixedEmbedding K (u : K)‖₊ fun x : mixedSpace K ↦ u • x :=
    lipschitzWith_smul _
  rw [← Set.image_smul]
  exact hC.isBounded_image (isBounded_normLeOne K)



open scoped Classical in
/-- **The norm-≤-one section of the ray fundamental domain is bounded.** It is carved out of a
finite union of unit translates of Mathlib's norm-≤-one region, and each translate is bounded
because the unit acts by a Lipschitz map. -/
theorem isBounded_rayFundamentalDomain_inter_normLeOne (𝔪 : Modulus K) :
    Bornology.IsBounded
      (rayFundamentalDomain 𝔪 ∩ {x : mixedSpace K | mixedEmbedding.norm x ≤ 1}) := by
  rw [rayFundamentalDomain_inter_normLeOne_eq]
  exact (Bornology.isBounded_iUnion.2 fun q ↦ isBounded_unitSMul_normLeOne _).subset
    Set.inter_subset_right





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
# Counting congruence-lattice points in the ray fundamental domain

Let `𝔪` be a modulus of a number field `K` and `I` an invertible fractional ideal.  This file
counts the points of a coset of `congruenceLattice 𝔪 I` inside the dilates of the norm-≤-one
section of `rayFundamentalDomain 𝔪`, with a power-saving error and — the point — with an implied
constant that does not depend on the coset.

Nothing here is new geometry.  The lattice-point count with a power-saving error takes a bounded
region whose frontier is Lipschitz parametrizable in codimension one, and the norm-≤-one section
of the ray fundamental domain has been shown to be exactly that; the congruence lattice has been
shown to be a full `ℤ`-lattice in the mixed space.  This file is the instantiation, and it exists
because the three inputs live in three different developments and the fit between them is the
step that a count of ideals in a fixed ray class actually consumes.

The count is stated for an arbitrary translate `ξ` rather than for the lattice itself because a
fixed ray class corresponds to one coset of the congruence lattice, so every class needs its own
instance of the estimate.  What the statement provides is a single `A` valid for *every* translate
at once, which is the form the class-by-class count consumes directly.

## Main results

* `TauCeti.GlobalNumberFields.exists_abs_ncard_smul_rayFundamentalDomain_inter_vadd_sub_le`: the
  points of any coset of `congruenceLattice 𝔪 I` in the dilate `c •` of the norm-≤-one section
  number `vol / covolume * c ^ [K:ℚ]` up to `O(c ^ ([K:ℚ] - 1))`, uniformly in the coset;
* `TauCeti.GlobalNumberFields.exists_abs_ncard_rayFundamentalDomain_inter_norm_le_inter_vadd_sub_le`
  — the same count graded by the norm: the main term is linear in `t` and the error is
  `O(t ^ (1 - 1 / [K:ℚ]))`.

## References

* S. Lang, *Algebraic Number Theory*, Chapter VI, §2.
-/

 section

open Bornology MeasureTheory Module NumberField NumberField.mixedEmbedding
open scoped Pointwise nonZeroDivisors

namespace TauCeti.GlobalNumberFields
end TauCeti.GlobalNumberFields
section TauCeti.GlobalNumberFields
open TauCeti TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

open scoped Classical in
/-- **The congruence-lattice count in the ray fundamental domain, uniformly in the coset.**  For
any coset `ξ +ᵥ congruenceLattice 𝔪 I`, the number of its points in the dilate
`c • (rayFundamentalDomain 𝔪 ∩ {norm ≤ 1})` is the volume ratio times `c ^ [K:ℚ]`, with an error
`O(c ^ ([K:ℚ] - 1))` whose implied constant is independent of both `c` and the coset.

The exponent is written `finrank ℝ (mixedSpace K)`, which is `[K:ℚ]` by
`NumberField.mixedEmbedding.finrank`; a consumer counting ideals by their absolute norm rewrites
along that equality. -/
theorem TauCeti.GlobalNumberFields.exists_abs_ncard_smul_rayFundamentalDomain_inter_vadd_sub_le (𝔪 : _root_.TauCeti.GlobalNumberFields.Modulus K)
    (I : (_root_.FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ A ≥ (0 : ℝ), ∀ (ξ : _root_.NumberField.mixedEmbedding.mixedSpace K) (c : ℝ), 1 ≤ c →
      |(((c • (_root_.TauCeti.GlobalNumberFields.rayFundamentalDomain 𝔪 ∩ {x : _root_.NumberField.mixedEmbedding.mixedSpace K | mixedEmbedding.norm x ≤ 1})) ∩
            (ξ +ᵥ (_root_.TauCeti.GlobalNumberFields.congruenceLattice 𝔪 I : _root_.Set (_root_.NumberField.mixedEmbedding.mixedSpace K)))).ncard : ℝ) -
          volume.real (_root_.TauCeti.GlobalNumberFields.rayFundamentalDomain 𝔪 ∩ {x : _root_.NumberField.mixedEmbedding.mixedSpace K | mixedEmbedding.norm x ≤ 1}) /
            _root_.ZLattice.covolume (_root_.TauCeti.GlobalNumberFields.congruenceLattice 𝔪 I) _root_.MeasureTheory.MeasureSpace.volume *
              c ^ _root_.Module.finrank ℝ (_root_.NumberField.mixedEmbedding.mixedSpace K)| ≤ A * c ^ (_root_.Module.finrank ℝ (_root_.NumberField.mixedEmbedding.mixedSpace K) - 1) :=
  -- `.2.2` is the Lipschitz-frontier conjunct; the boundedness hypothesis is a separate lemma
  _root_.TauCeti.exists_abs_ncard_smul_inter_vadd_sub_le
    (_root_.TauCeti.GlobalNumberFields.isBounded_rayFundamentalDomain_inter_normLeOne 𝔪)
    (_root_.TauCeti.GlobalNumberFields.isLipschitzParametrizable_frontier_rayFundamentalDomain 𝔪).2.2

open scoped Classical in
/-- **The congruence-lattice count graded by the norm, uniformly in the coset.**  For any coset
`ξ +ᵥ congruenceLattice 𝔪 I`, the number of its points in the ray fundamental domain of norm at
most `t` is `vol / covolume * t`, with an error `O(t ^ (1 - 1 / [K:ℚ]))` whose implied constant is
independent of both `t` and the coset.

This is the previous estimate regraded from dilations to norms: the main term is linear in `t`,
and the boundary exponent `[K:ℚ] - 1` becomes the power saving `1 / [K:ℚ]`.  Unlike
`ZLattice.covolume.tendsto_card_le_div'`, which gives a limit, it provides an explicit error
term, uniform in the coset. -/
theorem solution (𝔪 : _root_.TauCeti.GlobalNumberFields.Modulus K)
    (I : (_root_.FractionalIdeal (𝓞 K)⁰ K)ˣ) : ∃ A ≥ (0 : ℝ), ∀ (ξ : _root_.NumberField.mixedEmbedding.mixedSpace K) (t : ℝ), 1 ≤ t →
      |(((_root_.TauCeti.GlobalNumberFields.rayFundamentalDomain 𝔪 ∩ {x : _root_.NumberField.mixedEmbedding.mixedSpace K | mixedEmbedding.norm x ≤ t}) ∩
            (ξ +ᵥ (_root_.TauCeti.GlobalNumberFields.congruenceLattice 𝔪 I : _root_.Set (_root_.NumberField.mixedEmbedding.mixedSpace K)))).ncard : ℝ) -
          volume.real (_root_.TauCeti.GlobalNumberFields.rayFundamentalDomain 𝔪 ∩ {x : _root_.NumberField.mixedEmbedding.mixedSpace K | mixedEmbedding.norm x ≤ 1}) /
            _root_.ZLattice.covolume (_root_.TauCeti.GlobalNumberFields.congruenceLattice 𝔪 I) _root_.MeasureTheory.MeasureSpace.volume * t| ≤
        A * t ^ (1 - ((_root_.Module.finrank ℚ K : ℝ))⁻¹) := by
  obtain ⟨A, hA0, hA⟩ := _root_.TauCeti.GlobalNumberFields.exists_abs_ncard_smul_rayFundamentalDomain_inter_vadd_sub_le 𝔪 I
  simp only [_root_.NumberField.mixedEmbedding.finrank] at hA
  refine ⟨A, hA0, fun ξ t ht ↦ ?_⟩
  have ht0 : (0 : ℝ) < t := _root_.lt_of_lt_of_le _root_.one_pos ht
  have hn : 0 < _root_.Module.finrank ℚ K := _root_.Module.finrank_pos
  have hc1 : 1 ≤ t ^ ((_root_.Module.finrank ℚ K : ℝ))⁻¹ := _root_.Real.one_le_rpow ht (by positivity)
  have hc0 : (0 : ℝ) < t ^ ((_root_.Module.finrank ℚ K : ℝ))⁻¹ := _root_.lt_of_lt_of_le _root_.one_pos hc1
  have hcn : (t ^ ((_root_.Module.finrank ℚ K : ℝ))⁻¹) ^ _root_.Module.finrank ℚ K = t :=
    _root_.Real.rpow_inv_natCast_pow ht0.le hn.ne'
  have herr : (t ^ ((_root_.Module.finrank ℚ K : ℝ))⁻¹) ^ (_root_.Module.finrank ℚ K - 1) =
      t ^ (1 - ((_root_.Module.finrank ℚ K : ℝ))⁻¹) := by
    -- the two semantic steps: a natural power of an `rpow` is an `rpow`, and `rpow` exponents
    -- multiply; what remains is arithmetic in the exponent
    rw [← _root_.Real.rpow_natCast (t ^ ((_root_.Module.finrank ℚ K : ℝ))⁻¹) (_root_.Module.finrank ℚ K - 1), ← _root_.Real.rpow_mul ht0.le]
    congr 1
    have hn0 : (_root_.Module.finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    push_cast [_root_.Nat.cast_sub hn]
    field_simp
  -- dilating by `c` scales the norm by `c ^ [K:ℚ]`, so `c = t ^ (1 / [K:ℚ])` is the factor that
  -- presents the norm-≤-`t` section as a dilate of the norm-≤-one section
  have key := hA ξ (t ^ ((_root_.Module.finrank ℚ K : ℝ))⁻¹) hc1
  rwa [_root_.TauCeti.GlobalNumberFields.smul_rayFundamentalDomain_inter_normLeOne 𝔪 hc0, hcn, herr] at key

end TauCeti.GlobalNumberFields

end
end
