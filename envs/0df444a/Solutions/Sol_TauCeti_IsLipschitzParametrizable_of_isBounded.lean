-- Prove2me | solution 1 for TauCeti.IsLipschitzParametrizable.of_isBounded
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:29:04.332882+00:00
-- url     : https://prove2.me/submissions/4a6188a2-74aa-4deb-91e4-52e8d3358537

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_Topology_MetricSpace_LipschitzParametrizable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Theorems.Thm_TauCeti_IsLipschitzParametrizable_image_unitCube_of_contDiffOn

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

/-- Every subset of a Lipschitz-parametrizable set is Lipschitz parametrizable with the same
charts. -/
theorem TauCeti.IsLipschitzParametrizable.mono (hT : _root_.TauCeti.IsLipschitzParametrizable d T) (hST : S ⊆ T) :
    _root_.TauCeti.IsLipschitzParametrizable d S := by
  obtain ⟨n, C, f, hf, hT⟩ := _root_.TauCeti.isLipschitzParametrizable_iff.1 hT
  exact _root_.TauCeti.isLipschitzParametrizable_iff.2 ⟨n, C, f, hf, hST.trans hT⟩



















/-- **A bounded subset of a finite-dimensional real normed space is Lipschitz parametrizable in
the ambient dimension.** Linear coordinates carry the set into a box, and a box is the image of
the unit cube under an affine — hence `C¹` — map, so one chart suffices.

This is the trivial bound on the dimension: it is useful only for pieces of a set that are
genuinely lower dimensional for another reason, such as a bounded piece of a hyperplane. -/
theorem solution {E : Type*} [_root_.NormedAddCommGroup E] [_root_.NormedSpace ℝ E] [_root_.FiniteDimensional ℝ E]
    {S : _root_.Set E} (hS : _root_.Bornology.IsBounded S) :
    _root_.TauCeti.IsLipschitzParametrizable (_root_.Module.finrank ℝ E) S := by
  set n := _root_.Module.finrank ℝ E
  set e : E ≃L[ℝ] (_root_.Fin n → ℝ) :=
    _root_.ContinuousLinearEquiv.ofFinrankEq (_root_.Module.finrank_fin_fun ℝ).symm
  -- Coordinates carry `S` into the box `[-M, M] ^ n`, with `M ≥ 1` so that `2 * M ≠ 0`.
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp (e.lipschitz.isBounded_image hS)
  set M : ℝ := _root_.Max.max R 1
  have hM0 : (0 : ℝ) < M := _root_.lt_of_lt_of_le _root_.zero_lt_one (_root_.le_max_right _ _)
  have hcd : _root_.ContDiff ℝ 1 fun t : _root_.Fin n → ℝ ↦ e.symm fun i ↦ 2 * M * t i - M := by fun_prop
  refine .mono (.image_unitCube_of_contDiffOn (_root_.Fintype.card_fin n) hcd.contDiffOn) fun x hx ↦ ?_
  have key : ∀ i, -M ≤ e x i ∧ e x i ≤ M := fun i ↦ abs_le.mp <| by
    rw [← _root_.Real.norm_eq_abs]
    exact (_root_.norm_le_pi_norm (e x) i).trans ((hR _ ⟨x, hx, _root_.rfl⟩).trans (_root_.le_max_left _ _))
  -- The cube point is the coordinate vector of `x`, rescaled from `[-M, M]` to `[0, 1]`.
  -- Cube membership is two pointwise inequalities: `Set.mem_Icc` splits the interval and the
  -- order on `Fin n → ℝ` is pointwise, so `Pi.zero_apply` / `Pi.one_apply` name the endpoints.
  refine ⟨fun i ↦ (e x i + M) / (2 * M), Set.mem_Icc.mpr ⟨fun i ↦ ?_, fun i ↦ ?_⟩, ?_⟩
  · rw [_root_.Pi.zero_apply]
    exact _root_.div_nonneg (by linarith [(key i).1]) (by linarith)
  · rw [_root_.Pi.one_apply]
    exact (_root_.div_le_one (by linarith)).2 (by linarith [(key i).2])
  · -- The parametrisation sends the cube point back through `e.symm`, so the image equation is an
    -- equation in `E`; `e.symm_apply_eq` moves it to `Fin n → ℝ`, where it is coordinatewise.
    rw [e.symm_apply_eq]
    funext i
    rw [_root_.mul_div_cancel₀ _ (by positivity : (2 * M : ℝ) ≠ 0), _root_.add_sub_cancel_right]







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
