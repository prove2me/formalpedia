-- Prove2me | solution 1 for TauCeti.GlobalNumberFields.frontier_posRegion_subset
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:16:46.316085+00:00
-- url     : https://prove2.me/submissions/29bc8260-8aa8-405f-a384-42b8fa2c644f

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
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne
import Mathlib.NumberTheory.NumberField.ClassNumber
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
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.MetricSpace.HausdorffDimension

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Cutting a reflection-invariant subset of the mixed space at a finset of real places

Let `S` be a finset of real places and `A` a subset of the mixed space preserved by the reflection
`negAt {w}` of the real coordinate at each single place `w` of `S`.  The `2 ^ S.card` sign patterns
along `S` then cut `A` into pieces of equal volume, exhausting `A` up to the null set where some
coordinate of `S` vanishes.

Cutting `A` down to the points that are positive at every place of `S` therefore divides its
volume by `2 ^ S.card`, the real coordinates outside `S` staying free.  A set whose membership
depends on the real coordinates only through their absolute values is invariant at every real
place, and for `S` all of the real places the statement is then Mathlib's
`NumberField.mixedEmbedding.volume_eq_two_pow_mul_volume_plusPart`.

## Main results

* `TauCeti.NumberField.mixedEmbedding.isOpen_setOfPred_forall_mem_pos`: the points positive at
  every place of a finset of real places form an open set.
* `TauCeti.NumberField.mixedEmbedding.volume_eq_two_pow_mul_volume_inter_pos`: for a set invariant
  under reflection at each place of `S`, the volume is `2 ^ S.card` times the volume of the part
  that is positive at every place of `S`.
-/

 section

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

namespace TauCeti.NumberField.mixedEmbedding

variable {K : Type*} [Field K] [NumberField K]



omit [NumberField K] in
/-- The points positive at every place of `S` form an open set: it is a finite intersection of
open half spaces. -/
theorem isOpen_setOfPred_forall_mem_pos (S : Finset {w : InfinitePlace K // w.IsReal}) :
    IsOpen {x : mixedSpace K | ∀ w ∈ S, 0 < x.1 w} := by
  simp only [Set.ofPred_forall]
  exact isOpen_biInter_finset fun w _ ↦ isOpen_lt continuous_const (by fun_prop)



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









/-- The positivity region is open: it is a finite intersection of open half spaces. -/
theorem isOpen_posRegion (𝔪 : Modulus K) : IsOpen (posRegion 𝔪) := by
  rw [show posRegion 𝔪 = {x : mixedSpace K | ∀ w ∈ 𝔪.infinitePart, 0 < x.1 w} from
    Set.ext fun _ ↦ mem_posRegion]
  exact TauCeti.NumberField.mixedEmbedding.isOpen_setOfPred_forall_mem_pos 𝔪.infinitePart









/-! ### The fundamental domain -/













































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
end TauCeti.GlobalNumberFields
section TauCeti.GlobalNumberFields
open TauCeti TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- **The frontier of the positivity region lies in the prescribed coordinate hyperplanes.** The
region is cut out by finitely many strict inequalities, so a boundary point satisfies all of them
non-strictly yet must fail one of them: that coordinate vanishes. Mathlib's
`frontier_lt_subset_eq` is the single-inequality case; the content here is that a finite
intersection of such regions still confines its frontier to those level sets. -/
theorem solution (𝔪 : _root_.TauCeti.GlobalNumberFields.Modulus K) :
    _root_.frontier (_root_.TauCeti.GlobalNumberFields.posRegion 𝔪) ⊆ ⋃ w ∈ 𝔪.infinitePart, {x : _root_.NumberField.mixedEmbedding.mixedSpace K | x.1 w = 0} := by
  intro x hx
  -- The closure side: each half space `0 ≤ · w` is closed and contains the region.
  have hx1 : ∀ w ∈ 𝔪.infinitePart, 0 ≤ x.1 w := fun w hw ↦
    _root_.closure_minimal (fun _ hy ↦ (mem_posRegion.mp hy w hw).le)
      (_root_.isClosed_le _root_.continuous_const ((_root_.continuous_apply w).comp _root_.continuous_fst))
      (_root_.frontier_subset_closure hx)
  -- The interior side: the region is open, so a boundary point misses it outright.
  rw [(_root_.TauCeti.GlobalNumberFields.isOpen_posRegion 𝔪).frontier_eq] at hx
  have hx2 : ¬ ∀ w ∈ 𝔪.infinitePart, 0 < x.1 w := fun h ↦ hx.2 (mem_posRegion.mpr h)
  push _root_.Not at hx2
  obtain ⟨w, hw, hle⟩ := hx2
  exact _root_.Set.mem_biUnion hw (hle.antisymm (hx1 w hw))

















end TauCeti.GlobalNumberFields

end
end
