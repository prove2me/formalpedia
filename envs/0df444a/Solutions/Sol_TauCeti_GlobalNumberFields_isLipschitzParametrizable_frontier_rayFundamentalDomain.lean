-- Prove2me | solution 1 for TauCeti.GlobalNumberFields.isLipschitzParametrizable_frontier_rayFundamentalDomain
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:41:20.769315+00:00
-- url     : https://prove2.me/submissions/5442517f-f24d-4288-8511-806115d9e243

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_Algebra_Order_Ring_Units
import Definitions.Def_TauCeti_GroupTheory_Index_Basic
import Definitions.Def_TauCeti_NumberTheory_NumberField_CanonicalEmbedding_UnitAction
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
import Theorems.Thm_NumberField_mixedEmbedding_fundamentalCone_isLipschitzParametrizable_frontier_normLeOne
import Theorems.Thm_TauCeti_GlobalNumberFields_frontier_posRegion_subset
import Theorems.Thm_TauCeti_IsLipschitzParametrizable_of_isBounded
import Theorems.Thm_TauCeti_IsLipschitzParametrizable_union

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

theorem measurableSet_posRegion (𝔪 : Modulus K) : MeasurableSet (posRegion 𝔪) :=
  (isOpen_posRegion 𝔪).measurableSet







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

/-- The ray fundamental domain is measurable: it is the intersection of an open region with a
finite union of unit translates of Mathlib's measurable fundamental cone. -/
theorem measurableSet_rayFundamentalDomain (𝔪 : Modulus K) :
    MeasurableSet (rayFundamentalDomain 𝔪) := by
  let _ := (unitsCongruenceSubgroupSupTorsion 𝔪).fintypeQuotientOfFiniteIndex
  rw [rayFundamentalDomain_eq_iUnion]
  refine (measurableSet_posRegion 𝔪).inter (MeasurableSet.iUnion fun q ↦ ?_)
  rw [← Set.preimage_smul_inv]
  exact (measurableSet_fundamentalCone K).preimage (measurable_const_smul _)





























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
# Lipschitz-parametrizable sets

A set is Lipschitz parametrizable in dimension `d` when finitely many Lipschitz images of the
unit `d`-cube cover it.  This is the boundary regularity condition used in lattice-point counting:
a codimension-one parametrization gives quantitative control on how many lattice cells can meet a
boundary.

This file supplies the elementary API needed to assemble parametrizations: the property is
monotone in the set, is preserved by Lipschitz images, by locally Lipschitz images, by products
and by finite unions, and holds for finite sets.
It also supplies the way in from smoothness: a map that is `C¹` on the compact cube is Lipschitz
there, so the image of a cube of the right dimension is a single chart.
It also records the basic dimension consequence.  A Lipschitz-parametrizable subset of a
finite-dimensional real normed space has additive Haar measure zero whenever the parameter
dimension is strictly smaller than the ambient dimension.  The proof compares additive Haar
measure with Hausdorff measure and uses the fact that Lipschitz maps do not increase Hausdorff
dimension.

It also records the quantitative form of a single chart: cutting the unit `d`-cube into `m ^ d`
subcubes of side `1 / m` covers a Lipschitz image of it by `m ^ d` pieces of diameter `C / m`.
That is what turns a parametrization in a given dimension into a count.

## Main declarations

* `TauCeti.IsLipschitzParametrizable`: finite Lipschitz parametrizability by a
  unit cube;
* `TauCeti.isLipschitzParametrizable_iff`: the finite-chart characterization of the predicate;
* `TauCeti.IsLipschitzParametrizable.union`: closure under binary unions;
* `TauCeti.IsLipschitzParametrizable.image`: closure under Lipschitz images;
* `TauCeti.IsLipschitzParametrizable.image_of_locallyLipschitz`: closure under locally Lipschitz
  images, which is what a chart-by-chart compactness argument buys over `image`;
* `TauCeti.IsLipschitzParametrizable.iUnion`: closure under unions over a finite index type;
* `TauCeti.IsLipschitzParametrizable.prod`: a product is parametrized in the sum of the
  dimensions;
* `TauCeti.IsLipschitzParametrizable.image_unitCube_of_contDiffOn`: a unit cube's image under a
  map that is `C¹` on it is parametrized by that cube;
* `TauCeti.IsLipschitzParametrizable.of_isBounded`: a bounded subset of a finite-dimensional real
  normed space is parametrized in the ambient dimension;
* `TauCeti.IsLipschitzParametrizable.of_isBounded_of_subset_ker`: a bounded subset of a hyperplane
  is parametrized in codimension one;
* `TauCeti.IsLipschitzParametrizable.measure_zero`: a parametrized set has
  additive Haar measure zero below the ambient dimension;
* `LipschitzOnWith.exists_cover_image_unitCube`: a Lipschitz image of the unit `d`-cube is
  covered by `m ^ d` pieces of arbitrarily small diameter.

## References

* S. Lang, *Algebraic Number Theory*, Chapter VI, Section 2, which the definition and its use in
  the lattice-point estimate follow.
* C. Birkbeck, [*AINTLIB*](https://github.com/CBirkbeck/AINTLIB) at commit
  `db14b34cc5e3d79603e67c205dfa86b7b989000c` (Apache-2.0),
  `projects/Chebotarev/CebotarevDensity/ForMathlib/IdealCongruenceCount.lean`, whose
  `exists_lipschitz_cube_cover_hyperplane_slab` is the concrete precursor of
  `of_isBounded` and `of_isBounded_of_subset_ker`: it covers a bounded slab of a coordinate
  hyperplane of `ι → ℝ` by a single chart, through the same affine rescaling
  `c ↦ 2 * M * c - M` of the unit cube onto the box `[-M, M]`. The two lemmas here say the
  same thing without reference to coordinates, for any finite-dimensional real normed space
  and any hyperplane in it.
-/

 section

open MeasureTheory Set

namespace TauCeti



/-- A set is Lipschitz parametrizable in dimension `d` if and only if finitely many unit-cube
charts, all Lipschitz with a common constant on the unit cube, cover it. -/
theorem isLipschitzParametrizable_iff {E : Type*} [PseudoEMetricSpace E] {d : ℕ} {S : Set E} :
    IsLipschitzParametrizable d S ↔
      ∃ (n : ℕ) (C : NNReal) (f : Fin n → (Fin d → ℝ) → E),
        (∀ i, LipschitzOnWith C (f i) (Icc (0 : Fin d → ℝ) 1)) ∧
          S ⊆ ⋃ i, f i '' Icc (0 : Fin d → ℝ) 1 :=
  Iff.rfl

namespace IsLipschitzParametrizable

variable {E F : Type*} [PseudoEMetricSpace E] [PseudoEMetricSpace F]
  {d : ℕ} {S T : Set E}

/-- Every subset of a Lipschitz-parametrizable set is Lipschitz parametrizable with the same
charts. -/
theorem mono (hT : IsLipschitzParametrizable d T) (hST : S ⊆ T) :
    IsLipschitzParametrizable d S := by
  obtain ⟨n, C, f, hf, hT⟩ := isLipschitzParametrizable_iff.1 hT
  exact isLipschitzParametrizable_iff.2 ⟨n, C, f, hf, hST.trans hT⟩

/-- The empty set is Lipschitz parametrizable in every dimension. -/
@[simp]
theorem empty : IsLipschitzParametrizable d (∅ : Set E) := by
  exact isLipschitzParametrizable_iff.2 ⟨0, 0, Fin.elim0, fun i ↦ i.elim0, Set.empty_subset _⟩





/-- A finite union of sets parametrized in the same dimension is Lipschitz parametrizable. -/
theorem biUnion_finset {I : Type*} (s : Finset I) {A : I → Set E}
    (hA : ∀ i ∈ s, IsLipschitzParametrizable d (A i)) :
    IsLipschitzParametrizable d (⋃ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.set_biUnion_insert]
      exact (hA i (Finset.mem_insert_self i s)).union
        (ih fun j hj ↦ hA j (Finset.mem_insert_of_mem hj))

/-- A union over a finite index type of sets parametrized in dimension `d` is Lipschitz
parametrizable in dimension `d`. -/
theorem iUnion {I : Type*} [Finite I] {A : I → Set E}
    (hA : ∀ i, IsLipschitzParametrizable d (A i)) :
    IsLipschitzParametrizable d (⋃ i, A i) := by
  classical
  cases nonempty_fintype I
  rw [← Set.biUnion_univ, ← Finset.coe_univ, Finset.set_biUnion_coe]
  exact biUnion_finset Finset.univ fun i _ ↦ hA i





/-- The image of a Lipschitz-parametrizable set under a Lipschitz map is Lipschitz
parametrizable. -/
theorem image {g : E → F} {K : NNReal} (hg : LipschitzWith K g)
    (hS : IsLipschitzParametrizable d S) : IsLipschitzParametrizable d (g '' S) := by
  obtain ⟨n, C, f, hf, hSf⟩ := isLipschitzParametrizable_iff.1 hS
  refine isLipschitzParametrizable_iff.2
    ⟨n, K * C, fun i ↦ g ∘ f i, fun i ↦ hg.comp_lipschitzOnWith (hf i), ?_⟩
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨i, z, hz, rfl⟩ := Set.mem_iUnion.1 (hSf hx)
  exact Set.mem_iUnion.2 ⟨i, z, hz, rfl⟩





/-- **A bounded subset of a hyperplane is Lipschitz parametrizable in codimension one.** The
hyperplane is the kernel of a nonzero linear functional, a subspace of dimension
`finrank ℝ E - 1`; inside it the set is still bounded, because the inclusion is an isometry. -/
theorem of_isBounded_of_subset_ker {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E →ₗ[ℝ] ℝ} (hf : f ≠ 0) {S : Set E} (hS : Bornology.IsBounded S)
    (hSf : S ⊆ LinearMap.ker f) : IsLipschitzParametrizable (Module.finrank ℝ E - 1) S := by
  -- Pull `S` back to the kernel, parametrize it there, and push it forward again: `S` is the
  -- image of its own preimage exactly because it lies in the kernel.
  have hiso : Isometry (Subtype.val : LinearMap.ker f → E) := isometry_subtype_coe
  have h := (of_isBounded (hiso.antilipschitz.isBounded_preimage hS)).image hiso.lipschitz
  rwa [Set.image_preimage_eq_of_subset (by rwa [Subtype.range_coe]),
    Nat.eq_sub_of_add_eq (Module.Dual.finrank_ker_add_one_of_ne_zero hf)] at h





end IsLipschitzParametrizable

end TauCeti

namespace LipschitzOnWith

variable {E : Type*} [PseudoMetricSpace E]



end LipschitzOnWith

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
# Elementary frontier lemmas

Facts about `frontier` that carry no structure of their own: straddling, splitting a domain in
two, clinging to it from inside, the frontier of an image, and the frontier of a finite union.
Each is the topological core of a step that a boundary argument would otherwise carry out inside
a concrete space. The list is open-ended; nothing below depends on how many entries it has.

## A connected set that straddles a set meets its frontier

A preconnected set that meets both a set `V` and its complement must meet `frontier V`: it cannot
cross from the inside of `V` to the outside without touching the boundary. This is the
intermediate-value principle in its purely topological form, and it is the mechanism by which a
*path* leaving a set produces a *boundary point* of that set.

Mathlib records the two extreme cases — `frontier_eq_empty_iff` and `nonempty_frontier_iff` say
that in a preconnected *space* the frontier of `V` is empty exactly when `V` is `∅` or `univ` — but
not this relative form, which is the one an argument along a segment or a path needs. No hypothesis
is placed on `V`; only preconnectedness of the straddling set is used.

The proof is the standard clopen argument: the complement of `frontier V` is the disjoint union of
the two open sets `interior V` and `interior Vᶜ` (`compl_frontier_eq_union_interior`), so a
preconnected set avoiding the frontier lies inside one of them, and then it misses `V` entirely or
is contained in `V` entirely.

## Where the boundary of the image of one side of a split domain can lie

Split a set `U` into two pieces `s` and `t` that a map `f` sends to *disjoint open* sets, plus a
remainder `u`. Then `frontier (f '' s) ⊆ f '' u ∪ frontier (f '' U)`
(`TauCeti.frontier_image_subset_image_union_frontier_image`): the boundary of the image of one side
consists of images of the remainder — the cut — and of boundary points of the whole image, and of
nothing else.

The proof is a three-way case split. A point `p` of `frontier (f '' s)` lies in `closure (f '' U)`,
so if it is not on `frontier (f '' U)` it is a value `f w` with `w` in one of the three covering
sets. It cannot come from `s`, since `f '' s` is open and therefore disjoint from its own frontier;
and it cannot come from `t`, since `f '' t` is then an open neighbourhood of `p`, which must meet
`f '' s`, contradicting disjointness of the two images. So `w ∈ u`.

The source carries no topology; the sides enter topologically only through their images, which are
asked to be open and disjoint, and that is all the argument uses of them. What is asked of the
sides themselves is purely set-theoretic: `s ⊆ U` and the covering `U ⊆ s ∪ t ∪ u`. In particular
`t` need not lie in `U`, and neither side need be open or disjoint from the other. A consumer whose
map is open and injective on two disjoint open sides supplies both image hypotheses, as the
conformal one below does through the open mapping theorem and `Disjoint.image`.

## What a set's frontier sees of a subset

A subset `A` of a set `V` cannot reach `frontier V` except through its own frontier:

> `frontier V ∩ closure A = frontier V ∩ frontier A`

(`TauCeti.frontier_inter_closure_eq_frontier_inter_frontier`). The reason is that `closure A` is
`A ∪ frontier A`, and a point of `A` on `frontier V` is already on `frontier A`: it is adherent to
`A` and, since `interior A ⊆ interior V`, it is not interior to `A`. So the part of `frontier V`
that `A` clings to has two interchangeable descriptions — as the reach of `closure A`, and as the
meeting of two frontiers. The first is the one an argument about limits of points of `A` produces;
the second is the one a diameter estimate consumes, `frontier` being where the estimates of a
domain-splitting argument live.

## Consumers

The straddling, splitting and clinging lemmas serve Carathéodory's boundary correspondence for
conformal maps. The first does so through `TauCeti/Analysis/Normed/Module/DiamFrontier.lean`: a
ray leaving a bounded set crosses its frontier, which is what makes the frontier of such a set as
wide as the set itself. The second is the splitting step of
`TauCeti/Analysis/Complex/Conformal/CutDiameter.lean`, where `s` and `t` are the two sides of a
circular crosscut of a domain and `u` is the crosscut arc. The third is what lets
`TauCeti/Analysis/Complex/Conformal/ClusterSet.lean` identify the boundary piece that one side of
such a crosscut cuts off, whose description as a union of cluster sets is naturally a statement
about a closure. The image and finite-union lemmas are used quite differently, for a partial
homeomorphism of a real coordinate space and for the frontier of a finite union of unit translates
of a lattice region. Nothing here is specific to any of those uses; no lemma mentions a metric,
let alone a holomorphic map.

## Main results

* `IsPreconnected.inter_frontier_nonempty` — a preconnected set meeting both a set and its
  complement meets the frontier of that set.
* `TauCeti.frontier_image_subset_image_union_frontier_image` — for a set split into two sides with
  disjoint open images plus a remainder, the frontier of the image of the side lying in that set
  lies on the image of the remainder and on the frontier of the image of the whole.
* `TauCeti.frontier_inter_closure_eq_frontier_inter_frontier` — the frontier of a set meets the
  closure of a subset exactly where it meets that subset's frontier.
* `TauCeti.frontier_image_subset_of_closure_subset` — for an open injective map whose image
  closure adds at most a set `t`, the frontier of an image lies on the image of the frontier,
  together with `t`.
* `TauCeti.frontier_iUnion_subset` — the frontier of a union over a finite index type lies in the
  union of the frontiers.
-/

 section

namespace TauCeti

open Set

section Straddle

variable {X : Type*} [TopologicalSpace X] {S V : Set X}



end Straddle

section ImageSplit

variable {X Y : Type*} [TopologicalSpace Y] {f : X → Y} {U s t u : Set X}



end ImageSplit

section Inside

variable {X : Type*} [TopologicalSpace X] {A V : Set X}



end Inside

section OpenInjectiveImage

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} {s : Set X}
  {t : Set Y}



end OpenInjectiveImage

section FiniteUnion

variable {X : Type*} [TopologicalSpace X]

/-- **The frontier of a finite union lies in the union of the frontiers.** Finiteness is
essential, not a convenience of the proof: for an infinite union the inclusion fails — the
rationals are a countable union of singletons, each its own frontier, yet their union has
frontier all of `ℝ`. -/
theorem frontier_iUnion_subset {ι : Type*} [Finite ι] (A : ι → Set X) :
    frontier (⋃ i, A i) ⊆ ⋃ i, frontier (A i) := by
  intro x hx
  -- Finiteness enters through `closure_iUnion_of_finite`: a point adherent to the whole union
  -- is already adherent to one of the pieces.
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (closure_iUnion_of_finite A ▸ hx.1)
  -- The interior, by contrast, only grows with the union, so `x` misses `interior (A i)` too.
  exact Set.mem_iUnion.2 ⟨i, hi, fun hmem ↦ hx.2 (interior_mono (Set.subset_iUnion A i) hmem)⟩

end FiniteUnion

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



open scoped Classical in
/-- A bounded set of the mixed space on which one real coordinate vanishes is Lipschitz
parametrizable in codimension one: it lies in the kernel of the nonzero linear functional reading
that coordinate. -/
private theorem TauCeti.GlobalNumberFields.isLipschitzParametrizable_of_isBounded_of_fst_eq_zero
    (w : {w : _root_.NumberField.InfinitePlace K // w.IsReal}) {S : _root_.Set (_root_.NumberField.mixedEmbedding.mixedSpace K)}
    (hS : _root_.Bornology.IsBounded S) (hSw : ∀ x ∈ S, x.1 w = 0) :
    _root_.TauCeti.IsLipschitzParametrizable (_root_.Module.finrank ℝ (_root_.NumberField.mixedEmbedding.mixedSpace K) - 1) S :=
  _root_.TauCeti.IsLipschitzParametrizable.of_isBounded_of_subset_ker
    (f := (_root_.LinearMap.proj w).comp (_root_.LinearMap.fst ℝ _ _))
    (_root_.DFunLike.ne_iff.2 ⟨(_root_.Pi.single w 1, 0), by simp⟩) hS
    fun x hx ↦ LinearMap.mem_ker.mpr (hSw x hx)

open scoped Classical in
/-- The piece the positivity region contributes to a frontier, when paired with the closure of a
bounded set: `frontier_posRegion_subset` puts it inside finitely many coordinate hyperplanes, and
each of those slices is bounded, hence Lipschitz parametrizable in codimension one. -/
private theorem TauCeti.GlobalNumberFields.isLipschitzParametrizable_closure_inter_frontier_posRegion (𝔪 : _root_.TauCeti.GlobalNumberFields.Modulus K)
    {A : _root_.Set (_root_.NumberField.mixedEmbedding.mixedSpace K)} (hA : _root_.Bornology.IsBounded A) :
    _root_.TauCeti.IsLipschitzParametrizable (_root_.Module.finrank ℝ (_root_.NumberField.mixedEmbedding.mixedSpace K) - 1)
      (_root_.closure A ∩ _root_.frontier (_root_.TauCeti.GlobalNumberFields.posRegion 𝔪)) := by
  refine .mono (.biUnion_finset 𝔪.infinitePart
    (A := fun w ↦ _root_.closure A ∩ {x : _root_.NumberField.mixedEmbedding.mixedSpace K | x.1 w = 0}) fun w _ ↦
      _root_.TauCeti.GlobalNumberFields.isLipschitzParametrizable_of_isBounded_of_fst_eq_zero w
        (hA.closure.subset _root_.Set.inter_subset_left) fun x hx ↦ hx.2) ?_
  rintro x ⟨hx1, hx2⟩
  obtain ⟨w, hw, hxw⟩ := _root_.Set.mem_iUnion₂.1 (_root_.TauCeti.GlobalNumberFields.frontier_posRegion_subset 𝔪 hx2)
  exact _root_.Set.mem_iUnion₂.2 ⟨w, hw, hx1, hxw⟩

/-- **The norm-≤-one section of the ray fundamental domain**, as the positivity region cut by a
finite union of unit translates of Mathlib's norm-≤-one region. The unit action preserves the
mixed norm, so it commutes with the norm condition. -/
theorem TauCeti.GlobalNumberFields.rayFundamentalDomain_inter_normLeOne_eq (𝔪 : _root_.TauCeti.GlobalNumberFields.Modulus K) :
    _root_.TauCeti.GlobalNumberFields.rayFundamentalDomain 𝔪 ∩ {x : _root_.NumberField.mixedEmbedding.mixedSpace K | mixedEmbedding.norm x ≤ 1} =
      _root_.TauCeti.GlobalNumberFields.posRegion 𝔪 ∩ ⋃ q : (𝓞 K)ˣ ⧸ _root_.TauCeti.GlobalNumberFields.unitsCongruenceSubgroupSupTorsion 𝔪,
        _root_.TauCeti.GlobalNumberFields.rayUnitRepresentative 𝔪 q • _root_.NumberField.mixedEmbedding.fundamentalCone.normLeOne K := by
  ext x
  simp only [_root_.TauCeti.GlobalNumberFields.rayFundamentalDomain_eq_iUnion, _root_.Set.mem_inter_iff, _root_.Set.mem_iUnion,
    _root_.Set.mem_smul_set_iff_inv_smul_mem, _root_.Set.mem_ofPred_eq, _root_.NumberField.mixedEmbedding.norm_unit_smul]
  tauto

open scoped Classical in
/-- A unit translate of Mathlib's norm-≤-one region is bounded, because the unit acts by a
Lipschitz map. -/
private theorem TauCeti.GlobalNumberFields.isBounded_unitSMul_normLeOne (u : (𝓞 K)ˣ) :
    _root_.Bornology.IsBounded (u • _root_.NumberField.mixedEmbedding.fundamentalCone.normLeOne K) := by
  -- the unit action *is* multiplication by `mixedEmbedding K u`, so Mathlib's bound applies
  have hC : _root_.LipschitzWith ‖_root_.NumberField.mixedEmbedding K (u : K)‖₊ fun x : _root_.NumberField.mixedEmbedding.mixedSpace K ↦ u • x :=
    _root_.lipschitzWith_smul _
  rw [← _root_.Set.image_smul]
  exact hC.isBounded_image (_root_.NumberField.mixedEmbedding.fundamentalCone.isBounded_normLeOne K)

open scoped Classical in
/-- The frontier of a unit translate of Mathlib's norm-≤-one region is Lipschitz parametrizable in
codimension one: a unit acts by a homeomorphism, so this frontier is the Lipschitz image of
`frontier (normLeOne K)`. -/
private theorem TauCeti.GlobalNumberFields.isLipschitzParametrizable_frontier_unitSMul_normLeOne (u : (𝓞 K)ˣ) :
    _root_.TauCeti.IsLipschitzParametrizable (_root_.Module.finrank ℝ (_root_.NumberField.mixedEmbedding.mixedSpace K) - 1)
      (_root_.frontier (u • _root_.NumberField.mixedEmbedding.fundamentalCone.normLeOne K)) := by
  have hC : _root_.LipschitzWith ‖_root_.NumberField.mixedEmbedding K (u : K)‖₊ fun x : _root_.NumberField.mixedEmbedding.mixedSpace K ↦ u • x :=
    _root_.lipschitzWith_smul _
  refine .mono (.image hC (_root_.NumberField.mixedEmbedding.fundamentalCone.isLipschitzParametrizable_frontier_normLeOne K)) ?_
  rw [_root_.Set.image_smul]
  simp only [← _root_.Set.preimage_smul_inv]
  exact (_root_.continuous_const_mul _).frontier_preimage_subset _

open scoped Classical in
/-- **The norm-≤-one section of the ray fundamental domain is bounded.** It is carved out of a
finite union of unit translates of Mathlib's norm-≤-one region, and each translate is bounded
because the unit acts by a Lipschitz map. -/
theorem TauCeti.GlobalNumberFields.isBounded_rayFundamentalDomain_inter_normLeOne (𝔪 : _root_.TauCeti.GlobalNumberFields.Modulus K) :
    _root_.Bornology.IsBounded
      (_root_.TauCeti.GlobalNumberFields.rayFundamentalDomain 𝔪 ∩ {x : _root_.NumberField.mixedEmbedding.mixedSpace K | mixedEmbedding.norm x ≤ 1}) := by
  rw [_root_.TauCeti.GlobalNumberFields.rayFundamentalDomain_inter_normLeOne_eq]
  exact (_root_.Bornology.isBounded_iUnion.2 fun q ↦ _root_.TauCeti.GlobalNumberFields.isBounded_unitSMul_normLeOne _).subset
    _root_.Set.inter_subset_right

/-- **The norm-≤-one section of the ray fundamental domain is measurable**: the domain itself is
measurable and the mixed norm is continuous. -/
theorem TauCeti.GlobalNumberFields.measurableSet_rayFundamentalDomain_inter_normLeOne (𝔪 : _root_.TauCeti.GlobalNumberFields.Modulus K) :
    _root_.MeasurableSet (_root_.TauCeti.GlobalNumberFields.rayFundamentalDomain 𝔪 ∩ {x : _root_.NumberField.mixedEmbedding.mixedSpace K | mixedEmbedding.norm x ≤ 1}) :=
  (_root_.TauCeti.GlobalNumberFields.measurableSet_rayFundamentalDomain 𝔪).inter
    (_root_.measurableSet_le (_root_.NumberField.mixedEmbedding.continuous_norm K).measurable _root_.measurable_const)

open scoped Classical in
/-- **The norm-≤-one section of the ray fundamental domain is bounded and measurable, and its
frontier is Lipschitz parametrizable in codimension one.** The first and third conclusions are
exactly the two hypotheses `hDb` and `hDfr` of
`TauCeti.exists_abs_ncard_smul_inter_vadd_sub_le`, the lattice-point count with a power-saving
error, applied to the region counting the algebraic integers of a fixed ray class; the second is
what gives that region a measure at all. This is the analogue, for an arbitrary modulus, of
`isLipschitzParametrizable_frontier_normLeOne` for the trivial one, whose ray fundamental domain
is Mathlib's fundamental cone.

The section is `posRegion 𝔪` intersected with finitely many unit translates of `normLeOne K`.
The translates are bounded and each has a frontier that is a Lipschitz image of
`frontier (normLeOne K)`; the positivity region is unbounded, but `frontier_inter_subset` pairs
its frontier with the *closure of the translates*, so the piece it contributes is a bounded subset
of the finitely many coordinate hyperplanes prescribed by the infinite part of `𝔪`. -/
theorem solution (𝔪 : _root_.TauCeti.GlobalNumberFields.Modulus K) :
    _root_.Bornology.IsBounded
        (_root_.TauCeti.GlobalNumberFields.rayFundamentalDomain 𝔪 ∩ {x : _root_.NumberField.mixedEmbedding.mixedSpace K | mixedEmbedding.norm x ≤ 1}) ∧
      _root_.MeasurableSet (_root_.TauCeti.GlobalNumberFields.rayFundamentalDomain 𝔪 ∩ {x : _root_.NumberField.mixedEmbedding.mixedSpace K | mixedEmbedding.norm x ≤ 1}) ∧
        _root_.TauCeti.IsLipschitzParametrizable (_root_.Module.finrank ℝ (_root_.NumberField.mixedEmbedding.mixedSpace K) - 1)
          (_root_.frontier (_root_.TauCeti.GlobalNumberFields.rayFundamentalDomain 𝔪 ∩
            {x : _root_.NumberField.mixedEmbedding.mixedSpace K | mixedEmbedding.norm x ≤ 1})) := by
  refine ⟨_root_.TauCeti.GlobalNumberFields.isBounded_rayFundamentalDomain_inter_normLeOne 𝔪,
    _root_.TauCeti.GlobalNumberFields.measurableSet_rayFundamentalDomain_inter_normLeOne 𝔪, ?_⟩
  rw [_root_.TauCeti.GlobalNumberFields.rayFundamentalDomain_inter_normLeOne_eq, _root_.Set.inter_comm]
  set A : _root_.Set (_root_.NumberField.mixedEmbedding.mixedSpace K) := ⋃ q : (𝓞 K)ˣ ⧸ _root_.TauCeti.GlobalNumberFields.unitsCongruenceSubgroupSupTorsion 𝔪,
    _root_.TauCeti.GlobalNumberFields.rayUnitRepresentative 𝔪 q • _root_.NumberField.mixedEmbedding.fundamentalCone.normLeOne K
  have hAbdd : _root_.Bornology.IsBounded A :=
    _root_.Bornology.isBounded_iUnion.2 fun q ↦ _root_.TauCeti.GlobalNumberFields.isBounded_unitSMul_normLeOne _
  have hAfr : _root_.TauCeti.IsLipschitzParametrizable (_root_.Module.finrank ℝ (_root_.NumberField.mixedEmbedding.mixedSpace K) - 1) (_root_.frontier A) :=
    .mono (.iUnion fun q ↦ _root_.TauCeti.GlobalNumberFields.isLipschitzParametrizable_frontier_unitSMul_normLeOne _)
      (_root_.TauCeti.frontier_iUnion_subset _)
  exact .mono (.union (.mono hAfr _root_.Set.inter_subset_left)
    (_root_.TauCeti.GlobalNumberFields.isLipschitzParametrizable_closure_inter_frontier_posRegion 𝔪 hAbdd))
    (_root_.frontier_inter_subset A (_root_.TauCeti.GlobalNumberFields.posRegion 𝔪))

end TauCeti.GlobalNumberFields

end
end
