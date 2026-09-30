-- Prove2me | solution 1 for TauCeti.IsLipschitzParametrizable.prod
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:16:43.12684+00:00
-- url     : https://prove2.me/submissions/837567fa-56e9-441c-9f5c-bff7d4b5344c

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













/-- A product of parametrized sets is Lipschitz parametrizable in the sum of the dimensions. -/
theorem solution {G : Type*} [_root_.PseudoEMetricSpace G] {e : ℕ} {T : _root_.Set G}
    (hS : _root_.TauCeti.IsLipschitzParametrizable d S) (hT : _root_.TauCeti.IsLipschitzParametrizable e T) :
    _root_.TauCeti.IsLipschitzParametrizable (d + e) (S ×ˢ T) := by
  obtain ⟨m, C, f, hf, hSf⟩ := _root_.TauCeti.isLipschitzParametrizable_iff.1 hS
  obtain ⟨n, D, g, hg, hTg⟩ := _root_.TauCeti.isLipschitzParametrizable_iff.1 hT
  -- Reading off a block of coordinates is `1`-Lipschitz and carries the cube into the cube.
  have hlip : ∀ {a : ℕ} (σ : _root_.Fin a → _root_.Fin (d + e)),
      _root_.LipschitzOnWith 1 (fun (x : _root_.Fin (d + e) → ℝ) k ↦ x (σ k)) (_root_.Set.Icc 0 1) := fun _ ↦
    (_root_.LipschitzWith.of_edist_le fun x y ↦
      _root_.edist_pi_le_iff.2 fun k ↦ _root_.edist_le_pi_edist x y _).lipschitzOnWith
  have hmaps : ∀ {a : ℕ} (σ : _root_.Fin a → _root_.Fin (d + e)),
      _root_.Set.MapsTo (fun (x : _root_.Fin (d + e) → ℝ) k ↦ x (σ k)) (_root_.Set.Icc 0 1) (_root_.Set.Icc 0 1) :=
    fun _ _ hz ↦ ⟨fun _ ↦ hz.1 _, fun _ ↦ hz.2 _⟩
  refine _root_.TauCeti.isLipschitzParametrizable_iff.2 ⟨m * n, _root_.Max.max C D, fun p x ↦
    (f (finProdFinEquiv.symm p).1 fun k ↦ x (_root_.Fin.castAdd e k),
      g (finProdFinEquiv.symm p).2 fun k ↦ x (_root_.Fin.natAdd d k)),
    fun p ↦ _root_.LipschitzOnWith.prodMk ?_ ?_, ?_⟩
  · simpa [_root_.Function.comp_def] using (hf _).comp (hlip _) (hmaps _)
  · simpa [_root_.Function.comp_def] using (hg _).comp (hlip _) (hmaps _)
  · rintro ⟨u, v⟩ ⟨hu, hv⟩
    obtain ⟨i, a, ha, rfl⟩ := _root_.Set.mem_iUnion.1 (hSf hu)
    obtain ⟨j, b, hb, rfl⟩ := _root_.Set.mem_iUnion.1 (hTg hv)
    -- `Fin.append a b` is the cube point whose two blocks parametrize `u` and `v`.
    refine _root_.Set.mem_iUnion.2 ⟨_root_.finProdFinEquiv (i, j), _root_.Fin.append a b, ⟨?_, ?_⟩, by simp⟩
    · exact _root_.Fin.addCases (fun l ↦ by simpa using ha.1 l) fun l ↦ by simpa using hb.1 l
    · exact _root_.Fin.addCases (fun l ↦ by simpa using ha.2 l) fun l ↦ by simpa using hb.2 l















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
