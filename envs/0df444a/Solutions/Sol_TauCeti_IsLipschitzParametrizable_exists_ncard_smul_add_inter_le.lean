-- Prove2me | solution 1 for TauCeti.IsLipschitzParametrizable.exists_ncard_smul_add_inter_le
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:24:28.896453+00:00
-- url     : https://prove2.me/submissions/1cf4aafe-fd32-4cfd-ac42-c719bbb4902d

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_Topology_MetricSpace_LipschitzParametrizable
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Theorems.Thm_LipschitzOnWith_exists_cover_image_unitCube

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Counting points of a discrete additive subgroup

This file gives a uniform bound on the number of points of a discrete additive subgroup in a set
of bounded diameter.  Translating one point of the intersection to the origin embeds the
intersection into a closed ball of the same radius.

## Main results

* `AddSubgroup.finite_inter`: a discrete additive subgroup meets a bounded set in a finite set.
* `AddSubgroup.ncard_inter_le_ncard_closedBall_inter`: a set of diameter at most `r`
  carries at most as many points of a discrete additive subgroup as the closed ball of radius `r`
  centred at the origin.
-/

 section

open Bornology Metric Set

namespace AddSubgroup

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

/-- A discrete additive subgroup meets a bounded set in a finite set: it is closed and discrete,
and the bounded set is contained in its compact closure. -/
theorem finite_inter (L : AddSubgroup E) [DiscreteTopology L] {s : Set E} (hs : IsBounded s) :
    (s ∩ (L : Set E)).Finite :=
  Metric.finite_isBounded_inter_isClosed
    (SetLike.isDiscrete_iff_discreteTopology.2 ‹DiscreteTopology L›) hs
    AddSubgroup.isClosed_of_discrete

/-- A set whose points are pairwise at distance at most `r` carries at most as many points of a
discrete subgroup as the closed ball of radius `r` centred at the origin does.  Translating a
point of the intersection to the origin is what makes the bound uniform over all such sets. -/
theorem ncard_inter_le_ncard_closedBall_inter (L : AddSubgroup E) [DiscreteTopology L]
    {s : Set E} {r : ℝ} (hs : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ r) :
    (s ∩ (L : Set E)).ncard ≤ (closedBall (0 : E) r ∩ (L : Set E)).ncard := by
  rcases (s ∩ (L : Set E)).eq_empty_or_nonempty with h | ⟨z, hzs, hzL⟩
  · simp [h]
  refine Set.ncard_le_ncard_of_injOn (fun x ↦ x - z) ?_ (fun x _ y _ h ↦ by simpa using h)
    (L.finite_inter isBounded_closedBall)
  rintro x ⟨hxs, hxL⟩
  exact ⟨mem_closedBall_zero_iff.2 ((dist_eq_norm x z) ▸ hs x hxs z hzs),
    L.sub_mem hxL hzL⟩

end AddSubgroup

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
# Counting points of a discrete subgroup near a dilated Lipschitz-parametrizable set

Let `L` be a discrete additive subgroup of a proper normed real vector space `E`, and let `S ⊆ E` be
Lipschitz parametrizable in dimension `d`, that is, covered by finitely many Lipschitz images of
the unit `d`-cube.  Dilating `S` by a factor `c ≥ 1` and thickening it by a fixed bounded set `B`
produces a region that carries `O(c ^ d)` points of `L`.

This is the quantitative half of Lipschitz parametrizability.  When `d` is strictly smaller than
the ambient dimension, as in the codimension-one boundary application, it is a genuinely smaller
order than the `c ^ (dim E)` points carried by a dilated body and hence gives a power-saving error
term in a lattice-point count.  The thickening by `B` is what the application needs: the lattice
cells `x + F` that meet a dilated region `c • S` are exactly the `x ∈ L` lying in
`c • S + (-F)`, so a count of cells meeting the boundary of a dilated body is a count of the
points of `L` in such a region.

The proof subdivides the unit cube into `m ^ d` subcubes of side `1 / m`, with `m` of size
`c`, so that each chart maps a subcube into a set of diameter at most one after dilating by `c`.
Translation invariance bounds the number of points of `L` in any set of bounded diameter by a
constant, so the total count is at most a constant times the number `m ^ d` of subcubes.

## Main results

* `TauCeti.IsLipschitzParametrizable.finite_smul_add_inter`: a bounded thickening of a dilated
  Lipschitz-parametrizable set meets a discrete subgroup in a finite set.
* `TauCeti.IsLipschitzParametrizable.exists_ncard_smul_add_inter_le`: the explicit bound
  `#((c • S + B) ∩ L) ≤ A * c ^ d` for `c ≥ 1`, with `A` independent of `c`.
* `TauCeti.IsLipschitzParametrizable.isBigO_ncard_smul_add_inter`: the same bound as an
  asymptotic statement, `#((c • S + B) ∩ L) = O(c ^ d)` as `c → ∞`.

## References

* S. Lang, *Algebraic Number Theory*, Chapter VI, Section 2.
-/

 section

open Asymptotics Bornology Filter Metric Set
open scoped Pointwise Topology

namespace TauCeti.IsLipschitzParametrizable
end TauCeti.IsLipschitzParametrizable
section TauCeti.IsLipschitzParametrizable
open TauCeti TauCeti.IsLipschitzParametrizable

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- A bounded thickening of a dilated Lipschitz-parametrizable set meets a discrete subgroup in a
finite set. -/
theorem TauCeti.IsLipschitzParametrizable.finite_smul_add_inter {d : ℕ} {S : _root_.Set E}
    (hS : _root_.TauCeti.IsLipschitzParametrizable d S) (L : _root_.AddSubgroup E) [_root_.DiscreteTopology L]
    {B : _root_.Set E} (hB : _root_.Bornology.IsBounded B) (c : ℝ) :
    ((c • S + B) ∩ (L : _root_.Set E)).Finite := by
  obtain ⟨n, C, f, hf, hcov⟩ := _root_.TauCeti.isLipschitzParametrizable_iff.1 hS
  apply L.finite_inter
  apply _root_.isBounded_add
  · exact ((_root_.Bornology.isBounded_iUnion.2 fun i ↦
      ((isCompact_Icc.image_of_continuousOn (hf i).continuousOn).isBounded)).subset hcov).smul₀ c
  · exact hB

/-- **The boundary count.**  If `S` is Lipschitz parametrizable in dimension `d` and `B` is
bounded, then for `c ≥ 1` the thickened dilate `c • S + B` contains at most `A * c ^ d` points of
a discrete subgroup `L`, with the constant `A` independent of `c`.

With `B = -F` for a bounded fundamental domain `F` of `L`, the left-hand side counts the cells of
`L` that meet `c • S`; taking `S` to be the frontier of a body and `d` its codimension-one
parametrization dimension is what produces a power-saving error in a lattice-point count. -/
theorem solution {d : ℕ} {S : _root_.Set E}
    (hS : _root_.TauCeti.IsLipschitzParametrizable d S) (L : _root_.AddSubgroup E) [_root_.DiscreteTopology L]
    {B : _root_.Set E} (hB : _root_.Bornology.IsBounded B) :
    ∃ A ≥ (0 : ℝ), ∀ c : ℝ, 1 ≤ c →
      (((c • S + B) ∩ (L : _root_.Set E)).ncard : ℝ) ≤ A * c ^ d := by
  obtain ⟨n, C, f, hf, hcov⟩ := _root_.TauCeti.isLipschitzParametrizable_iff.1 hS
  obtain ⟨r, hr⟩ := hB.subset_closedBall 0
  have hrB : ∀ x ∈ B, _root_.Dist.dist x 0 ≤ r := fun x hx ↦ _root_.Metric.mem_closedBall.1 (hr hx)
  set ρ : ℝ := 1 + 2 * r with hρ
  set N : ℕ := (_root_.Metric.closedBall (0 : E) ρ ∩ (L : _root_.Set E)).ncard
  refine ⟨n * ((C : ℝ) + 2) ^ d * N, by positivity, fun c hc ↦ ?_⟩
  have hc0 : (0 : ℝ) < c := _root_.lt_of_lt_of_le _root_.one_pos hc
  -- Cut each edge of the unit cube into `m` pieces, so that each of the `m ^ d` subcubes has
  -- image of diameter at most `c * C / m ≤ 1` after dilating by `c`.
  set m : ℕ := ⌈c * (C : ℝ)⌉₊ + 1 with hm
  have hm0 : 0 < m := _root_.Nat.succ_pos _
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hcm : c * (C : ℝ) / m ≤ 1 := by
    refine (_root_.div_le_one hmR).2 ?_
    have := _root_.Nat.le_ceil (c * (C : ℝ))
    rw [hm]
    push_cast
    linarith
  choose T hTcov hTdist using fun i ↦ (hf i).exists_cover_image_unitCube hm0
  -- The thickened dilates of the pieces cover `c • S + B`, and each has diameter at most `ρ`.
  set P : _root_.Fin n × (_root_.Fin d → _root_.Fin m) → _root_.Set E := fun p ↦ c • T p.1 p.2 + B with hP
  have hPcov : c • S + B ⊆ ⋃ p, P p := by
    rintro u hu
    rw [_root_.Set.mem_add] at hu
    obtain ⟨a, ha, b, hb, rfl⟩ := hu
    obtain ⟨s, hs, rfl⟩ := ha
    obtain ⟨i, hi⟩ := _root_.Set.mem_iUnion.1 (hcov hs)
    obtain ⟨k, hk⟩ := _root_.Set.mem_iUnion.1 (hTcov i hi)
    exact _root_.Set.mem_iUnion.2 ⟨(i, k), _root_.Set.mem_add.2
      ⟨c • s, _root_.Set.smul_mem_smul_set hk, b, hb, _root_.rfl⟩⟩
  have hPdist : ∀ p, ∀ u ∈ P p, ∀ v ∈ P p, _root_.Dist.dist u v ≤ ρ := by
    rintro ⟨i, k⟩ u hu v hv
    rw [hP, _root_.Set.mem_add] at hu hv
    obtain ⟨a, ⟨w, hw, rfl⟩, b, hb, rfl⟩ := hu
    obtain ⟨a', ⟨w', hw', rfl⟩, b', hb', rfl⟩ := hv
    have hchart : _root_.Dist.dist (c • w) (c • w') ≤ 1 := by
      rw [_root_.dist_smul₀, _root_.Real.norm_of_nonneg hc0.le]
      calc c * _root_.Dist.dist w w' ≤ c * ((C : ℝ) / m) := by gcongr; exact hTdist i k w hw w' hw'
        _ = c * (C : ℝ) / m := by ring
        _ ≤ 1 := hcm
    calc _root_.Dist.dist (c • w + b) (c • w' + b')
        ≤ _root_.Dist.dist (c • w) (c • w') + _root_.Dist.dist b b' := _root_.dist_add_add_le _ _ _ _
      _ ≤ 1 + (_root_.Dist.dist b 0 + _root_.Dist.dist 0 b') := by gcongr; exact _root_.dist_triangle _ _ _
      _ ≤ 1 + (r + r) := by
          gcongr
          exacts [hrB b hb, _root_.dist_comm (0 : E) b' ▸ hrB b' hb']
      _ = ρ := by rw [hρ]; ring
  -- Count: cover, then bound the points of `L` in each of the `n * m ^ d` pieces by `N`.
  have hfinite := hS.finite_smul_add_inter L hB c
  have hcount : hfinite.toFinset.card ≤ n * m ^ d * N := by
    rw [← _root_.Set.ncard_eq_toFinset_card _ hfinite]
    calc ((c • S + B) ∩ (L : _root_.Set E)).ncard
        ≤ (⋃ p, P p ∩ (L : _root_.Set E)).ncard := by
          refine _root_.Set.ncard_le_ncard ?_ (_root_.Set.finite_iUnion fun p ↦
            L.finite_inter (_root_.Metric.isBounded_iff.2 ⟨ρ, fun _ hu _ hv ↦ hPdist p _ hu _ hv⟩))
          rw [← _root_.Set.iUnion_inter]
          exact _root_.Set.inter_subset_inter_left _ hPcov
      _ ≤ ∑ p, (P p ∩ (L : _root_.Set E)).ncard := _root_.Set.ncard_iUnion_le_of_fintype _
      _ ≤ ∑ _p : _root_.Fin n × (_root_.Fin d → _root_.Fin m), N :=
          _root_.Finset.sum_le_sum fun p _ ↦
            _root_.AddSubgroup.ncard_inter_le_ncard_closedBall_inter L (hPdist p)
      _ = n * m ^ d * N := by simp
  -- The number `m ^ d` of subcubes is at most `(C + 2) ^ d * c ^ d`.
  have hmc : (m : ℝ) ≤ c * ((C : ℝ) + 2) := by
    have h₁ : ((⌈c * (C : ℝ)⌉₊ : ℕ) : ℝ) < c * (C : ℝ) + 1 :=
      _root_.Nat.ceil_lt_add_one (by positivity)
    rw [hm]
    push_cast
    nlinarith
  calc (((c • S + B) ∩ (L : _root_.Set E)).ncard : ℝ)
        = (hfinite.toFinset.card : ℝ) := by rw [_root_.Set.ncard_eq_toFinset_card _ hfinite]
    _ ≤ ((n * m ^ d * N : ℕ) : ℝ) := by exact_mod_cast hcount
    _ = (n : ℝ) * (m : ℝ) ^ d * N := by push_cast; ring
    _ ≤ (n : ℝ) * (c * ((C : ℝ) + 2)) ^ d * N := by gcongr
    _ = (n * ((C : ℝ) + 2) ^ d * N) * c ^ d := by rw [_root_.mul_pow]; ring



end TauCeti.IsLipschitzParametrizable

end
end
