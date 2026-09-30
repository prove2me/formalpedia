-- Prove2me | solution 1 for TauCeti.exists_abs_ncard_smul_inter_vadd_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:36:51.89199+00:00
-- url     : https://prove2.me/submissions/b03ba0b2-c18f-43e3-b7e8-b31427084ecd

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_Topology_MetricSpace_LipschitzParametrizable
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
import Theorems.Thm_TauCeti_IsLipschitzParametrizable_exists_ncard_smul_add_inter_le
import Theorems.Thm_TauCeti_abs_ncard_inter_mul_sub_measureReal_le

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Fundamental domains of integer spans

This file records geometric properties of the standard fundamental domain associated to a basis.
Its convexity makes lattice cells preconnected, so cells crossing the boundary of a set can be
detected by their intersection with the frontier in lattice-point counting arguments.

## Main results

* `ZSpan.convex_fundamentalDomain`: the fundamental domain of a real basis is convex.
* `ZSpan.eq_of_sub_mem_fundamentalDomain`: two integer-span translates placing a point in the
  fundamental domain are equal.
-/

 section

open Module Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}

/-- The fundamental domain of a basis is convex: it is cut out by the conditions
`b.repr x i ∈ [0, 1)`, one convex condition per coordinate. -/
theorem _root_.ZSpan.convex_fundamentalDomain (β : Basis ι ℝ E) :
    Convex ℝ (ZSpan.fundamentalDomain β) := by
  intro x hx y hy a t ha ht hat
  rw [ZSpan.mem_fundamentalDomain] at hx hy ⊢
  intro i
  simpa using convex_Ico (0 : ℝ) 1 (hx i) (hy i) ha ht hat

/-- Two vectors in the integer span that translate the same point into the fundamental domain
in subtraction form are equal. -/
theorem _root_.ZSpan.eq_of_sub_mem_fundamentalDomain [Finite ι] (β : Basis ι ℝ E)
    {x w₁ w₂ : E} (hw₁ : w₁ ∈ Submodule.span ℤ (Set.range β))
    (hw₂ : w₂ ∈ Submodule.span ℤ (Set.range β))
    (h₁ : x - w₁ ∈ ZSpan.fundamentalDomain β)
    (h₂ : x - w₂ ∈ ZSpan.fundamentalDomain β) : w₁ = w₂ := by
  have hn₁ : -w₁ ∈ Submodule.span ℤ (Set.range β) := neg_mem hw₁
  have hn₂ : -w₂ ∈ Submodule.span ℤ (Set.range β) := neg_mem hw₂
  have subtype_vadd (w : E) (hw : w ∈ Submodule.span ℤ (Set.range β)) :
      (⟨w, hw⟩ : Submodule.span ℤ (Set.range β)) +ᵥ x = w + x := rfl
  have heq : (⟨-w₁, hn₁⟩ : Submodule.span ℤ (Set.range β)) = ⟨-w₂, hn₂⟩ :=
    (ZSpan.exist_unique_vadd_mem_fundamentalDomain β x).unique
      (by rw [subtype_vadd]; simpa only [sub_eq_add_neg, add_comm] using h₁)
      (by rw [subtype_vadd]; simpa only [sub_eq_add_neg, add_comm] using h₂)
  exact neg_injective (congrArg Subtype.val heq)

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



end Counting

section Lattice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]
  {μ : Measure E} [μ.IsAddHaarMeasure]

private theorem TauCeti.abs_ncard_smul_inter_vadd_sub_le_aux {D F : _root_.Set E} {ξ : E} {c : ℝ}
    (hDb : _root_.Bornology.IsBounded D) (hc : 1 ≤ c) (hF₀ : (0 : E) ∈ F) (hFpc : _root_.IsPreconnected F)
    (hFb : _root_.Bornology.IsBounded F) (hFm : _root_.MeasurableSet F) (hcov : _root_.ZLattice.covolume L μ = μ.real F)
    (hFu : ∀ x : E, ∀ w₁ ∈ (L : _root_.Set E), ∀ w₂ ∈ (L : _root_.Set E), x - w₁ ∈ F → x - w₂ ∈ F → w₁ = w₂)
    (hFe : ∀ x : E, ∃ w ∈ (L : _root_.Set E), x - w ∈ F) :
    |(((c • D) ∩ (ξ +ᵥ (L : _root_.Set E))).ncard : ℝ) -
        μ.real D / _root_.ZLattice.covolume L μ * c ^ _root_.Module.finrank ℝ E| ≤
      (((c • _root_.frontier D + (F + -F)) ∩ (L : _root_.Set E)).ncard : ℝ) := by
  have hκ : 0 < μ.real F := hcov ▸ _root_.ZLattice.covolume_pos L μ
  have hc0 : (0 : ℝ) < c := _root_.lt_of_lt_of_le _root_.one_pos hc
  -- The count only depends on `ξ` modulo `L`, so reduce the representative into `F`: the slack
  -- the boundary estimate must absorb is then `F + -F`, not a set depending on `ξ`.
  obtain ⟨w, hwL, hvF⟩ := hFe (-ξ)
  have hvξ : -ξ - w + ξ = -w := by abel
  set v : E := -ξ - w
  -- translating by `v` carries the coset onto `L`, turning the count into a lattice-point count
  rw [hcov, ← _root_.Set.ncard_vadd_set v ((c • D) ∩ (ξ +ᵥ (L : _root_.Set E))), _root_.Set.vadd_set_inter, _root_.vadd_vadd,
    hvξ, _root_.vadd_coe_set (L.neg_mem hwL)]
  have hvol : μ.real (v +ᵥ c • D) = c ^ _root_.Module.finrank ℝ E * μ.real D := by
    rw [_root_.MeasureTheory.measureReal_def, _root_.MeasureTheory.measure_vadd, _root_.MeasureTheory.Measure.addHaar_smul, _root_.ENNReal.toReal_mul,
      _root_.ENNReal.toReal_ofReal (_root_.abs_nonneg _), _root_.abs_of_nonneg (by positivity), _root_.MeasureTheory.measureReal_def]
  have hkey := _root_.TauCeti.abs_ncard_inter_mul_sub_measureReal_le (μ := μ) (L := L) hF₀ hFpc hFb hFm hFu hFe
    ((hDb.smul₀ c).vadd v)
  rw [hvol] at hkey
  have hfr : _root_.frontier (c • D) = c • _root_.frontier D := by
    have h := (_root_.isHomeomorph_smul₀ (α := E) hc0.ne').image_frontier D
    simpa [_root_.Set.image_smul] using h.symm
  have hfrv : _root_.frontier (v +ᵥ c • D) = v +ᵥ c • _root_.frontier D := by
    rw [← hfr]
    exact (_root_.IsHomeomorph.image_frontier (_root_.Homeomorph.addLeft v).isHomeomorph (c • D)).symm
  -- a cell meeting the frontier of the translate is counted by the fixed thickened frontier
  have hsub : _root_.frontier (v +ᵥ c • D) + -F ⊆ c • _root_.frontier D + (F + -F) := by
    rw [hfrv]
    rintro _ ⟨_, ⟨y, hy, rfl⟩, z, hz, rfl⟩
    exact ⟨y, hy, v + z, ⟨v, hvF, z, hz, _root_.rfl⟩, by simp [_root_.vadd_eq_add, _root_.add_comm, _root_.add_left_comm]⟩
  have hbadfin : ((c • _root_.frontier D + (F + -F)) ∩ (L : _root_.Set E)).Finite :=
    L.toAddSubgroup.finite_inter
      (_root_.isBounded_add ((hDb.closure.subset _root_.frontier_subset_closure).smul₀ c)
        (_root_.isBounded_add hFb hFb.neg))
  have hrw : (((v +ᵥ c • D) ∩ (L : _root_.Set E)).ncard : ℝ) -
      μ.real D / μ.real F * c ^ _root_.Module.finrank ℝ E =
      ((((v +ᵥ c • D) ∩ (L : _root_.Set E)).ncard : ℝ) * μ.real F - c ^ _root_.Module.finrank ℝ E * μ.real D) /
        μ.real F := by
    field_simp
  refine _root_.le_of_mul_le_mul_right (_root_.le_trans (_root_.le_of_eq ?_) (hkey.trans ?_)) hκ
  · rw [hrw, _root_.abs_div, _root_.abs_of_pos hκ, _root_.div_mul_cancel₀ _ hκ.ne']
  · gcongr

/-- **Lattice points of a coset in a dilated body, uniformly in the coset.** For a bounded set `D`
whose frontier is Lipschitz parametrizable in dimension `n - 1`, the number of points of *any*
coset `ξ +ᵥ L` lying in `c • D` is `μ D / covolume L μ * c ^ n` up to `A * c ^ (n - 1)`, with `A`
independent of both `c ≥ 1` **and** the translate `ξ`.

Uniformity in `ξ` is the point, and it is not formal: the error is governed by the lattice cells
meeting the boundary of the translated body, while a translate ranges over all of `E`, which is
unbounded.

This is what lets a count be run over each coset of a sublattice with a single implied constant,
as a count of ideals in a fixed ray class requires. -/
theorem solution {D : _root_.Set E} (hDb : _root_.Bornology.IsBounded D)
    (hDfr : _root_.TauCeti.IsLipschitzParametrizable (_root_.Module.finrank ℝ E - 1) (_root_.frontier D)) :
    ∃ A ≥ (0 : ℝ), ∀ (ξ : E) (c : ℝ), 1 ≤ c →
      |(((c • D) ∩ (ξ +ᵥ (L : _root_.Set E))).ncard : ℝ) -
          μ.real D / _root_.ZLattice.covolume L μ * c ^ _root_.Module.finrank ℝ E| ≤ A * c ^ (_root_.Module.finrank ℝ E - 1) := by
  classical
  -- A fundamental domain for `L`, with the properties the estimate below consumes. Tiling is
  -- taken in subtraction form, which is the idiom the count uses.
  set b := _root_.Module.Free.chooseBasis ℤ L with hb
  set β := b.ofZLatticeBasis ℝ L with hβ
  set F := _root_.ZSpan.fundamentalDomain β with hF
  have hmem : ∀ w : E, w ∈ (L : _root_.Set E) ↔ w ∈ _root_.Submodule.span ℤ (_root_.Set.range β) := fun w ↦ by
    rw [hβ, b.ofZLatticeBasis_span ℝ]
    exact _root_.Iff.rfl
  have hF₀ : (0 : E) ∈ F := by simp [hF, _root_.ZSpan.mem_fundamentalDomain]
  have hFpc : _root_.IsPreconnected F := (_root_.ZSpan.convex_fundamentalDomain β).isPreconnected
  have hFb : _root_.Bornology.IsBounded F := _root_.ZSpan.fundamentalDomain_isBounded β
  have hFm : _root_.MeasurableSet F := _root_.ZSpan.fundamentalDomain_measurableSet β
  have hFu : ∀ x : E, ∀ w₁ ∈ (L : _root_.Set E), ∀ w₂ ∈ (L : _root_.Set E), x - w₁ ∈ F → x - w₂ ∈ F →
      w₁ = w₂ := fun _ w₁ h₁ w₂ h₂ k₁ k₂ ↦
    _root_.ZSpan.eq_of_sub_mem_fundamentalDomain β ((hmem w₁).mp h₁) ((hmem w₂).mp h₂) k₁ k₂
  have hFe : ∀ x : E, ∃ w ∈ (L : _root_.Set E), x - w ∈ F := fun x ↦
    ⟨(_root_.ZSpan.floor β x : E), (hmem _).mpr (_root_.ZSpan.floor β x).2,
      _root_.ZSpan.fract_mem_fundamentalDomain β x⟩
  have hcov : _root_.ZLattice.covolume L μ = μ.real F :=
    _root_.ZLattice.covolume_eq_measure_fundamentalDomain L μ (_root_.ZLattice.isAddFundamentalDomain b μ)
  -- The slack `F + -F` is one fixed bounded set, and is what makes `A` independent of `ξ`.
  obtain ⟨A, hA0, hA⟩ := hDfr.exists_ncard_smul_add_inter_le L.toAddSubgroup
    (_root_.isBounded_add hFb hFb.neg)
  exact ⟨A, hA0, fun ξ c hc ↦
    (_root_.TauCeti.abs_ncard_smul_inter_vadd_sub_le_aux hDb hc hF₀ hFpc hFb hFm hcov hFu hFe).trans (hA c hc)⟩




end Lattice

end TauCeti

end
end
