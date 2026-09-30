-- Prove2me | solution 1 for TauCeti.abs_ncard_inter_mul_sub_measureReal_le
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:24:32.44135+00:00
-- url     : https://prove2.me/submissions/05208604-9663-4a94-b250-f08a55f40a75

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Theorems.Thm_IsPreconnected_inter_frontier_nonempty
import Theorems.Thm_MeasureTheory_Measure_measure_biUnion_sub_mem

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
# Counting the lattice points of a dilated body, with a boundary-order error

Let `L` be a `ℤ`-lattice in an `n`-dimensional real normed space `E`, let `μ` be an additive Haar
measure on `E`, and let `D` be a bounded set whose frontier is Lipschitz parametrizable in
dimension `n - 1`.  When `0 < n`, the resulting error is power-saving. Dilating `D` by `c`
multiplies its volume by `c ^ n`, and each point of `L` in `c • D` accounts for one cell of the
lattice, of volume `covolume L μ`.  So

```text
#(c • D ∩ L) = μ D / covolume L μ * c ^ n + O(c ^ (n - 1)) as c → ∞.
```

Mathlib's `ZLattice.covolume.tendsto_card_div_pow'` assumes only that the frontier of the body is
null, which gives the limit but no error term at all.  An error term is what a counting argument
needs when the count is one term of a larger asymptotic, and it is what the stronger frontier
hypothesis buys.

## The argument

Fix a fundamental domain `F` for `L`, and call `w + F` the *cell* at a lattice point `w`.  The
cells tile `E`, so the volume of a set `X` is squeezed between the total volume of the cells
contained in `X` and the total volume of the cells meeting `X`, that is, between `#A * μ F` and
`#B * μ F` where

```text
A = {w ∈ L | w + F ⊆ X},   B = {w ∈ L | (w + F) ∩ X ≠ ∅}.
```

Since `0 ∈ F`, a lattice point lies in its own cell, so `A ⊆ X ∩ L ⊆ B` and the count `#(X ∩ L)`
is squeezed between the same two numbers.  Both quantities therefore differ by at most `#(B \ A)`
cells.  A cell counted by `B` and not by `A` meets `X` and its complement; being convex it is
preconnected, so it meets `frontier X` (`IsPreconnected.inter_frontier_nonempty`).  Hence
`B \ A` embeds in the lattice points of the thickened frontier `frontier X + -F`.  That is
`abs_ncard_inter_mul_sub_measureReal_le`, and it holds for any bounded `X`, with no regularity
hypothesis on the frontier: the boundary term is not yet estimated, only identified.

Taking `X = c • D` and `F` the fundamental domain of a basis of `L`, the thickened frontier is
`c • frontier D + -F`, whose lattice points number `O(c ^ (n - 1))` by the boundary count
`TauCeti.IsLipschitzParametrizable.exists_ncard_smul_add_inter_le`.  This is the only place the
Lipschitz hypothesis is used, and the only source of the error term.

## Main results

* `TauCeti.abs_ncard_inter_mul_sub_measureReal_le`: for any bounded set `X`, the count of lattice
  points of `X` times the volume of a fundamental domain `F` differs from the volume of `X` by at
  most the volume of `F` times the number of lattice points of `frontier X + -F`.
* `TauCeti.exists_abs_ncard_smul_inter_vadd_sub_le`: for `c ≥ 1` and *any* coset `ξ +ᵥ L`,
  `|#(c • D ∩ (ξ +ᵥ L)) - μ D / covolume L μ * c ^ n| ≤ A * c ^ (n - 1)`, with `A` independent of
  `c` **and** of `ξ`.
* `TauCeti.isBigO_ncard_smul_inter_sub`: that bound at `ξ = 0`, as an asymptotic statement.
## References

* S. Lang, *Algebraic Number Theory*, Chapter VI, Section 2.
* The coset-uniform count follows C. Birkbeck and R. Brasca,
  [*AINTLIB*](https://github.com/CBirkbeck/AINTLIB) at commit
  `db14b34cc5e3d79603e67c205dfa86b7b989000c` (Apache-2.0),
  `projects/Chebotarev/CebotarevDensity/ForMathlib/IdealCongruenceCount.lean`, theorem
  `exists_card_coset_inter_smul_sub_volume_mul_rpow_le`: the same statement, and the same
  reduction of the translate into a fundamental domain.
-/

 section

open Asymptotics Bornology Filter MeasureTheory Module Set Submodule
open scoped ENNReal Pointwise Topology

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

section Counting

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
  [MeasurableSpace E] [BorelSpace E] {L : Submodule ℤ E} [DiscreteTopology L]
  {μ : Measure E} [μ.IsAddRightInvariant] [IsLocallyFiniteMeasure μ] {F X : Set E}

/-- **Counting lattice points by cells.**  Let `F` be a bounded measurable preconnected set
containing `0` whose lattice translates `w + F`, for `w` in a discrete `L`, tile `E`.  Then for
every bounded set `X` the number of lattice points of `X`, weighted by the volume of `F`, differs
from the volume of `X` by at most the volume of `F` times the number of lattice points in the
thickened frontier `frontier X + -F`.

The hypotheses on `F` say exactly that it is a fundamental domain of the shape a counting argument
uses: `hFu` and `hFe` are uniqueness and existence of the cell containing a point, `hF₀` puts a
lattice point in its own cell, and preconnectedness is what makes a cell straddling `X` meet its
frontier.  No regularity is asked of `X`, and none of `frontier X`: the boundary term is
identified here and estimated by the caller. -/
theorem solution
    (hF₀ : (0 : E) ∈ F) (hFpc : _root_.IsPreconnected F) (hFb : _root_.Bornology.IsBounded F) (hFm : _root_.MeasurableSet F)
    (hFu : ∀ x : E, ∀ w₁ ∈ (L : _root_.Set E), ∀ w₂ ∈ (L : _root_.Set E), x - w₁ ∈ F → x - w₂ ∈ F → w₁ = w₂)
    (hFe : ∀ x : E, ∃ w ∈ (L : _root_.Set E), x - w ∈ F)
    (hXb : _root_.Bornology.IsBounded X) :
    |((X ∩ (L : _root_.Set E)).ncard : ℝ) * μ.real F - μ.real X| ≤
      (((_root_.frontier X + -F) ∩ (L : _root_.Set E)).ncard : ℝ) * μ.real F := by
  classical
  set A : _root_.Set E := {w | w ∈ (L : _root_.Set E) ∧ {y : E | y - w ∈ F} ⊆ X}
  set B : _root_.Set E := {w | w ∈ (L : _root_.Set E) ∧ ({y : E | y - w ∈ F} ∩ X).Nonempty}
  have hself : ∀ w : E, w ∈ {y : E | y - w ∈ F} := fun w ↦ by simpa using hF₀
  have hdisj : ∀ w₁ ∈ (L : _root_.Set E), ∀ w₂ ∈ (L : _root_.Set E), w₁ ≠ w₂ →
      _root_.Disjoint {y : E | y - w₁ ∈ F} {y : E | y - w₂ ∈ F} := fun w₁ h₁ w₂ h₂ hne ↦
    Set.disjoint_left.mpr fun y hy₁ hy₂ ↦ hne (hFu y w₁ h₁ w₂ h₂ hy₁ hy₂)
  have hBsub : B ⊆ (X + -F) ∩ (L : _root_.Set E) := by
    rintro w ⟨hwL, y, hyF, hyX⟩
    exact ⟨⟨y, hyX, -(y - w), by simpa using hyF, by simp⟩, hwL⟩
  have hBfin : B.Finite :=
    (L.toAddSubgroup.finite_inter (_root_.isBounded_add hXb hFb.neg)).subset hBsub
  have hAB : A ⊆ B := fun w hw ↦ ⟨hw.1, ⟨w, hself w, hw.2 (hself w)⟩⟩
  have hAfin : A.Finite := hBfin.subset hAB
  -- the cells of `A` lie in `X`, and the cells of `B` cover `X`
  have hAmeas : μ (⋃ w ∈ hAfin.toFinset, {y : E | y - w ∈ F}) = A.ncard * μ F := by
    rw [_root_.MeasureTheory.Measure.measure_biUnion_sub_mem μ hFm hdisj
        (fun w hw ↦ (hAfin.mem_toFinset.mp hw).1), _root_.Set.ncard_eq_toFinset_card _ hAfin]
  have hBmeas : μ (⋃ w ∈ hBfin.toFinset, {y : E | y - w ∈ F}) = B.ncard * μ F := by
    rw [_root_.MeasureTheory.Measure.measure_biUnion_sub_mem μ hFm hdisj
        (fun w hw ↦ (hBfin.mem_toFinset.mp hw).1), _root_.Set.ncard_eq_toFinset_card _ hBfin]
  have hlow : (A.ncard : ℝ≥0∞) * μ F ≤ μ X := by
    rw [← hAmeas]
    exact _root_.MeasureTheory.measure_mono (_root_.Set.iUnion₂_subset fun w hw ↦ (hAfin.mem_toFinset.mp hw).2)
  have hup : μ X ≤ (B.ncard : ℝ≥0∞) * μ F := by
    rw [← hBmeas]
    refine _root_.MeasureTheory.measure_mono fun x hx ↦ ?_
    obtain ⟨w, hwL, hwF⟩ := hFe x
    exact Set.mem_iUnion₂.mpr ⟨w, hBfin.mem_toFinset.mpr ⟨hwL, ⟨x, hwF, hx⟩⟩, hwF⟩
  -- a cell straddling `X` meets its frontier, so it is counted by the boundary term
  have hbadfin : ((_root_.frontier X + -F) ∩ (L : _root_.Set E)).Finite :=
    L.toAddSubgroup.finite_inter
      (_root_.isBounded_add (hXb.closure.subset _root_.frontier_subset_closure) hFb.neg)
  have hBA : B \ A ⊆ (_root_.frontier X + -F) ∩ (L : _root_.Set E) := by
    rintro w ⟨⟨hwL, hmeet⟩, hnA⟩
    obtain ⟨z, hzc, hzX⟩ := Set.not_subset.mp fun h ↦ hnA ⟨hwL, h⟩
    obtain ⟨y, hyc, hyfr⟩ :=
      ((_root_.Homeomorph.subRight w).isPreconnected_preimage.mpr hFpc).inter_frontier_nonempty
        hmeet ⟨z, hzc, hzX⟩
    exact ⟨⟨y, hyfr, -(y - w), by simpa using hyc, by simp⟩, hwL⟩
  -- assemble: the count is squeezed between the two cell counts, as is the measure
  have hAX : A ⊆ X ∩ (L : _root_.Set E) := fun w hw ↦ ⟨hw.2 (hself w), hw.1⟩
  have hXB : X ∩ (L : _root_.Set E) ⊆ B := fun w hw ↦ ⟨hw.2, ⟨w, hself w, hw.1⟩⟩
  have hκ : (0 : ℝ) ≤ μ.real F := _root_.ENNReal.toReal_nonneg
  have h1 : (A.ncard : ℝ) * μ.real F ≤ μ.real X := by
    have h := _root_.ENNReal.toReal_mono hXb.measure_lt_top.ne hlow
    rwa [_root_.ENNReal.toReal_mul, _root_.ENNReal.toReal_natCast] at h
  have h2 : μ.real X ≤ (B.ncard : ℝ) * μ.real F := by
    have h := _root_.ENNReal.toReal_mono
      (_root_.ENNReal.mul_ne_top (_root_.ENNReal.natCast_ne_top _) hFb.measure_lt_top.ne) hup
    rwa [_root_.ENNReal.toReal_mul, _root_.ENNReal.toReal_natCast] at h
  have h3 : (A.ncard : ℝ) ≤ ((X ∩ (L : _root_.Set E)).ncard : ℝ) :=
    Nat.cast_le.mpr (_root_.Set.ncard_le_ncard hAX (L.toAddSubgroup.finite_inter hXb))
  have h4 : ((X ∩ (L : _root_.Set E)).ncard : ℝ) ≤ (B.ncard : ℝ) :=
    Nat.cast_le.mpr (_root_.Set.ncard_le_ncard hXB hBfin)
  have h5 : (B.ncard : ℝ) - A.ncard ≤ (((_root_.frontier X + -F) ∩ (L : _root_.Set E)).ncard : ℝ) := by
    have hle := _root_.Set.ncard_le_ncard hBA hbadfin
    rw [_root_.Set.ncard_sdiff hAB hAfin] at hle
    have hAle : A.ncard ≤ B.ncard := _root_.Set.ncard_le_ncard hAB hBfin
    rw [← _root_.Nat.cast_le (α := ℝ), _root_.Nat.cast_sub hAle] at hle
    linarith
  have e1 := _root_.mul_le_mul_of_nonneg_right h4 hκ
  have e2 := _root_.mul_le_mul_of_nonneg_right h3 hκ
  have e3 := _root_.mul_le_mul_of_nonneg_right h5 hκ
  rw [_root_.sub_mul] at e3
  rw [_root_.abs_le]
  constructor <;> linarith

end Counting

section Lattice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]
  {μ : Measure E} [μ.IsAddHaarMeasure]








end Lattice

end TauCeti

end
end
