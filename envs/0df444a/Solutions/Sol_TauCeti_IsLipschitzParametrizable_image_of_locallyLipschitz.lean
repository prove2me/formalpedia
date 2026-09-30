-- Prove2me | solution 1 for TauCeti.IsLipschitzParametrizable.image_of_locallyLipschitz
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:16:39.818399+00:00
-- url     : https://prove2.me/submissions/4659d34f-82a7-4c37-b36e-d6ad1e88a3da

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_Topology_MetricSpace_LipschitzParametrizable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.MetricSpace.HausdorffDimension

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
end TauCeti
section TauCeti
open TauCeti



/-- A set is Lipschitz parametrizable in dimension `d` if and only if finitely many unit-cube
charts, all Lipschitz with a common constant on the unit cube, cover it. -/
theorem TauCeti.isLipschitzParametrizable_iff {E : Type*} [_root_.PseudoEMetricSpace E] {d : ℕ} {S : _root_.Set E} :
    _root_.TauCeti.IsLipschitzParametrizable d S ↔
      ∃ (n : ℕ) (C : _root_.NNReal) (f : _root_.Fin n → (_root_.Fin d → ℝ) → E),
        (∀ i, _root_.LipschitzOnWith C (f i) (_root_.Set.Icc (0 : _root_.Fin d → ℝ) 1)) ∧
          S ⊆ ⋃ i, f i '' _root_.Set.Icc (0 : _root_.Fin d → ℝ) 1 :=
  _root_.Iff.rfl

namespace TauCeti.IsLipschitzParametrizable
end TauCeti.IsLipschitzParametrizable
section IsLipschitzParametrizable
open TauCeti TauCeti.IsLipschitzParametrizable

variable {E F : Type*} [PseudoEMetricSpace E] [PseudoEMetricSpace F]
  {d : ℕ} {S T : Set E}

























/-- The image of a Lipschitz-parametrizable set under a locally Lipschitz map is Lipschitz
parametrizable. -/
theorem solution {E F : Type*} [_root_.PseudoMetricSpace E] [_root_.PseudoMetricSpace F] {d : ℕ}
    {S : _root_.Set E} {g : E → F} (hg : _root_.LocallyLipschitz g) (hS : _root_.TauCeti.IsLipschitzParametrizable d S) :
    _root_.TauCeti.IsLipschitzParametrizable d (g '' S) := by
  obtain ⟨n, C, f, hf, hSf⟩ := _root_.TauCeti.isLipschitzParametrizable_iff.1 hS
  -- Each chart has compact image, so `g` is Lipschitz on it with some constant `D i`.
  choose D hD using fun i ↦ hg.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_Icc.image_of_continuousOn (hf i).continuousOn)
  -- Finitely many charts, so the constants `D i * C` admit a common bound.
  refine _root_.TauCeti.isLipschitzParametrizable_iff.2 ⟨n, Finset.univ.sup fun i ↦ D i * C, fun i ↦ g ∘ f i,
    fun i ↦ ((hD i).comp (hf i) (_root_.Set.mapsTo_image _ _)).weaken
      (_root_.Finset.le_sup (f := fun i ↦ D i * C) (_root_.Finset.mem_univ i)), ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨i, z, hz, rfl⟩ := _root_.Set.mem_iUnion.1 (hSf hx)
  exact _root_.Set.mem_iUnion.2 ⟨i, z, hz, _root_.rfl⟩



end IsLipschitzParametrizable

end TauCeti

namespace LipschitzOnWith
end LipschitzOnWith
section LipschitzOnWith
open LipschitzOnWith

variable {E : Type*} [PseudoMetricSpace E]



end LipschitzOnWith

end
end
