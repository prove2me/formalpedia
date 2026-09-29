-- Prove2me | solution 1 for RiemannZetaOrders.zeta_analyticOrderAt_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T17:54:22.804264+00:00
-- url     : https://prove2.me/submissions/df95c710-7a62-45b2-bbb1-56469ac6a824

import Mathlib

set_option maxHeartbeats 2000000

-- ===== Salt.SW.BoxFold =====
section
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# The SW rung, wave S2 — the functional-equation fold (node A1-c)

Design: `docs/exploration/s2-trackA-design.md`, the A1-c node — the reflection that
folds the *low* half-box of critical-strip zeros onto the *high* half-box, turning the
half-box count (`zeta_box_count_half`-shaped, owned by `Salt/SW/BoxCount.lean`) into a
count over the *full* strip box `0 < Re ρ < 1`, `|Im ρ − t| ≤ 1`.

Namespace `Salt.SW`. Depends only on mathlib. Stated **parametric** in the half-box
count (as hypotheses `hfin`/`hhalf`), so the house composes it with `BoxCount`'s keystone
at the ceremony — this module imports no `.All` aggregator and no sibling wave file.

## The symmetry (worked out)

Two facings of the zeta symmetry live in mathlib; A1-c uses the **completed** functional
equation `Λ(1 − s) = Λ(s)` (`completedRiemannZeta_one_sub`, hypothesis-free) as its
engine, because `Λ` reflects with *no* side conditions and the only auxiliary factor is
`Gammaℝ`, whose zeros sit at `s = −2n` (all with `Re ≤ 0`, **outside** the open strip),
so it is analytic and nonvanishing there (`Gammaℝ_ne_zero_of_re_pos`). Writing
`ζ = Λ · (Gammaℝ)⁻¹` (with `(Gammaℝ)⁻¹` entire, `differentiable_Gammaℝ_inv`) transfers the
reflection from `Λ` to `ζ` *with multiplicity*:

* `zeta_order_completed` : `analyticOrderAt ζ w = analyticOrderAt Λ w` on the strip.
* `completed_order_one_sub` : `analyticOrderAt Λ (1−ρ) = analyticOrderAt Λ ρ` — the
  affine change of variables `s ↦ 1−s` (deriv `−1 ≠ 0`, `analyticOrderAt_comp_of_deriv_ne_zero`)
  composed with `Λ ∘ (1−·) = Λ`.
* **`zeta_analyticOrderAt_one_sub`** (the multiplicity keystone, item 4) :
  `analyticOrderAt ζ (1−ρ) = analyticOrderAt ζ ρ` for `0 < Re ρ < 1`. The order — hence the
  divisor — is *preserved* by the reflection.

The map `ρ ↦ 1 − ρ` reflects `Re` about `1/2` and *negates* `Im` (`Im(1−ρ) = −Im ρ`), so it
carries the low box `{0 < Re < 1/2, |Im − t| ≤ 1}` into `{1/2 < Re < 1, |Im − (−t)| ≤ 1}`, a
subset of the high box **at ordinate `−t`**. The imaginary sign flip costs nothing: the
half-box bound holds at every ordinate `u` and `log(|−t|+2) = log(|t|+2)`. The seam `Re = 1/2`
is fixed by the reflection but is absorbed into the high box `[1/2, 1)`, so the partition
`(0,1/2) ⊔ [1/2,1) = (0,1)` double-counts nothing.

## The case enumeration (spec item 1)

`zeta_fe_factor_ne_zero` records the honest nonvanishing of the *un-completed* factor
`2 · (2π)^{−ρ} · Γ(ρ) · cos(πρ/2)` of `riemannZeta_one_sub` on the open strip, case by case:
`2 ≠ 0`; `(2π)^{−ρ} ≠ 0` (nonzero base); `Γ(ρ) ≠ 0` (poles of `Γ` at `−ℕ`, all `Re ≤ 0`,
outside the strip); `cos(πρ/2) ≠ 0` (its zeros are the *odd integers* `ρ = 2k+1`, whose real
parts `2k+1 ∉ (0,1)`). It is not on the core path (the completed route needs no `cos`); it is
the documented "which zeros sit where" answer and an independent proof of the set symmetry.

## The fold (item 3)

**`zeta_box_count_full`** : given `hfin : ∀ u, (zBoxHi u).Finite` and
`hhalf : ∀ u, zBoxCount (zBoxHi u) ≤ C·log(|u|+2)` (the parametric half-box count, in
with-multiplicity `zBoxCount = ∑ᶠ divisor` form), the full-box count obeys
`zBoxCount (zBoxFull t) ≤ 2·C·log(|t|+2)`.
-/

namespace Salt.SW

open Complex Filter Topology

/-! ## 1. Analyticity of the completed zeta at strip points -/

/-- `Λ = completedRiemannZeta` is analytic away from its two poles `0, 1`. -/
lemma analyticAt_completedZeta {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    AnalyticAt ℂ completedRiemannZeta s := by
  have hset : ({0, 1} : Set ℂ).Finite := (Set.finite_singleton _).insert _
  have hopen : IsOpen (({0, 1} : Set ℂ)ᶜ) := hset.isClosed.isOpen_compl
  have hmem : s ∈ (({0, 1} : Set ℂ)ᶜ) := by
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h0, h1⟩
  have hdon : DifferentiableOn ℂ completedRiemannZeta (({0, 1} : Set ℂ)ᶜ) := by
    intro z hz
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz
    exact (differentiableAt_completedZeta hz.1 hz.2).differentiableWithinAt
  exact hdon.analyticOnNhd hopen s hmem

/-! ## 2. The multiplicity keystone (item 4) -/

/-- On the strip (`s ≠ 0, 1`, `Re s > 0`), `ζ` and `Λ` have the same vanishing order, since
`ζ = Λ · (Gammaℝ)⁻¹` with `(Gammaℝ)⁻¹` entire and nonvanishing there. -/
lemma zeta_order_completed {w : ℂ} (hw0 : w ≠ 0) (hw1 : w ≠ 1) (hwre : 0 < w.re) :
    analyticOrderAt riemannZeta w = analyticOrderAt completedRiemannZeta w := by
  have hev : riemannZeta =ᶠ[𝓝 w] completedRiemannZeta * (fun s => (Gammaℝ s)⁻¹) := by
    filter_upwards [eventually_ne_nhds hw0] with s hs
    rw [Pi.mul_apply, riemannZeta_def_of_ne_zero hs, div_eq_mul_inv]
  rw [analyticOrderAt_congr hev]
  have hΛ : AnalyticAt ℂ completedRiemannZeta w := analyticAt_completedZeta hw0 hw1
  have hG : AnalyticAt ℂ (fun s : ℂ => (Gammaℝ s)⁻¹) w :=
    (differentiable_Gammaℝ_inv.differentiableOn.analyticOnNhd isOpen_univ) w (Set.mem_univ w)
  have hGne : (fun s : ℂ => (Gammaℝ s)⁻¹) w ≠ 0 := inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hwre)
  rw [analyticOrderAt_mul hΛ hG, hG.analyticOrderAt_eq_zero.mpr hGne, add_zero]

/-- `Λ`'s functional equation `Λ(1−s) = Λ(s)`, read as order preservation. -/
lemma completed_order_one_sub (ρ : ℂ) :
    analyticOrderAt completedRiemannZeta (1 - ρ) = analyticOrderAt completedRiemannZeta ρ := by
  have hg : AnalyticAt ℂ (fun s : ℂ => 1 - s) ρ := by fun_prop
  have hd : HasDerivAt (fun s : ℂ => 1 - s) (-1) ρ := by simpa using (hasDerivAt_id ρ).const_sub 1
  have hg' : deriv (fun s : ℂ => 1 - s) ρ ≠ 0 := by rw [hd.deriv]; norm_num
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero (f := completedRiemannZeta) hg hg'
  have hfun : (completedRiemannZeta ∘ fun s : ℂ => 1 - s) = completedRiemannZeta := by
    funext s; simp only [Function.comp_apply, completedRiemannZeta_one_sub]
  rw [hfun] at hcomp
  exact hcomp.symm

/-- **The multiplicity keystone (A1-c, item 4).** The reflection `ρ ↦ 1 − ρ` preserves the
vanishing order of `ζ` on the open strip: `analyticOrderAt ζ (1 − ρ) = analyticOrderAt ζ ρ`. -/
lemma zeta_analyticOrderAt_one_sub {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    analyticOrderAt riemannZeta (1 - ρ) = analyticOrderAt riemannZeta ρ := by
  have hρ0 : ρ ≠ 0 := by rintro rfl; simp at h0
  have hρ1 : ρ ≠ 1 := by rintro rfl; simp at h1
  have hsubre : 0 < (1 - ρ).re := by rw [Complex.sub_re, Complex.one_re]; linarith
  have hs0 : (1 - ρ) ≠ 0 := fun h => hρ1 (sub_eq_zero.mp h).symm
  have hs1 : (1 - ρ) ≠ 1 := fun h => hρ0 (sub_eq_self.mp h)
  rw [zeta_order_completed hs0 hs1 hsubre, completed_order_one_sub ρ,
    ← zeta_order_completed hρ0 hρ1 h0]

/-- **The set-level zero symmetry** (item 1, from the multiplicity keystone). On the open
strip, `ζ(1 − ρ) = 0 ↔ ζ ρ = 0`. -/
lemma zeta_zero_one_sub_iff {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    riemannZeta (1 - ρ) = 0 ↔ riemannZeta ρ = 0 := by
  have hρ1 : ρ ≠ 1 := by rintro rfl; simp at h1
  have hs1 : (1 - ρ) ≠ 1 := by
    intro h; exact (by rintro rfl; simp at h0 : ρ ≠ 0) (sub_eq_self.mp h)
  have haρ : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ (by simpa using hρ1)
  have has : AnalyticAt ℂ riemannZeta (1 - ρ) := analyticOn_riemannZeta (1 - ρ) (by simpa using hs1)
  rw [← has.analyticOrderAt_ne_zero, zeta_analyticOrderAt_one_sub h0 h1]
  exact haρ.analyticOrderAt_ne_zero

/-! ## 3. The un-completed factor: the honest cos/Γ case enumeration (item 1) -/

/-- **The case enumeration.** The `riemannZeta_one_sub` factor
`2 · (2π)^{−ρ} · Γ(ρ) · cos(πρ/2)` is nonzero on the open strip `0 < Re ρ < 1`. -/
lemma zeta_fe_factor_ne_zero {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    2 * (2 * (Real.pi : ℂ)) ^ (-ρ) * Gamma ρ * cos ((Real.pi : ℂ) * ρ / 2) ≠ 0 := by
  have hπ0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) ?_) ?_
  · -- `(2π)^{−ρ} ≠ 0`: a power of a nonzero base
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl (mul_ne_zero two_ne_zero hπ0)
  · -- `Γ(ρ) ≠ 0`: its poles `−m` all have `Re ≤ 0`
    refine Complex.Gamma_ne_zero fun m => ?_
    intro heq
    rw [heq] at h0
    simp only [Complex.neg_re, Complex.natCast_re] at h0
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  · -- `cos(πρ/2) ≠ 0`: its zeros are the odd integers `2k+1 ∉ (0,1)`
    rw [Complex.cos_ne_zero_iff]
    intro k heq
    have hmul : (Real.pi : ℂ) * ρ = (2 * (k : ℂ) + 1) * (Real.pi : ℂ) := by
      linear_combination 2 * heq
    have hρeq : ρ = 2 * (k : ℂ) + 1 := by
      rw [mul_comm ((2 : ℂ) * (k : ℂ) + 1) (Real.pi : ℂ)] at hmul
      exact mul_left_cancel₀ hπ0 hmul
    have hre : (2 * (k : ℂ) + 1).re = 2 * (k : ℝ) + 1 := by
      simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
        Complex.one_re, Complex.re_ofNat, Complex.im_ofNat]
      ring
    rw [hρeq, hre] at h0 h1
    have e0 : (-1 : ℤ) < 2 * k := by exact_mod_cast (by linarith : (-1 : ℝ) < 2 * (k : ℝ))
    have e1 : 2 * k < 0 := by exact_mod_cast (by linarith : (2 : ℝ) * (k : ℝ) < 0)
    omega

/-! ## 4. The box zero-sets, the with-multiplicity count, and the fold (item 3) -/

/-- Multiplicity of a `ζ`-zero (`0` at non-zeros), cast to `ℝ`; the divisor summand. -/
noncomputable def zZeroMult (ρ : ℂ) : ℝ := ((analyticOrderAt riemannZeta ρ).toNat : ℝ)

lemma zZeroMult_nonneg (ρ : ℂ) : 0 ≤ zZeroMult ρ := Nat.cast_nonneg _

/-- The *low* half-box: `ζ`-zeros with `0 < Re ρ < 1/2`, `|Im ρ − t| ≤ 1`. -/
def zBoxLo (t : ℝ) : Set ℂ :=
  {ρ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 / 2 ∧ |ρ.im - t| ≤ 1}

/-- The *high* half-box (seam `Re = 1/2` lives here): `1/2 ≤ Re ρ < 1`, `|Im ρ − t| ≤ 1`. -/
def zBoxHi (t : ℝ) : Set ℂ :=
  {ρ | riemannZeta ρ = 0 ∧ 1 / 2 ≤ ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1}

/-- The *full* strip box: `0 < Re ρ < 1`, `|Im ρ − t| ≤ 1`. -/
def zBoxFull (t : ℝ) : Set ℂ :=
  {ρ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1}

/-- The with-multiplicity zero count over a region (the divisor finsum). -/
noncomputable def zBoxCount (S : Set ℂ) : ℝ := ∑ᶠ ρ ∈ S, zZeroMult ρ

/-- Monotonicity of the count under set inclusion (nonneg summand, finite superset). -/
lemma zBoxCount_mono {A B : Set ℂ} (hAB : A ⊆ B) (hB : B.Finite) :
    zBoxCount A ≤ zBoxCount B := by
  have hA : A.Finite := hB.subset hAB
  simp only [zBoxCount]
  rw [finsum_mem_eq_finite_toFinset_sum _ hA, finsum_mem_eq_finite_toFinset_sum _ hB]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Set.Finite.toFinset_mono hAB) ?_
  intro i _ _
  exact zZeroMult_nonneg i

/-- **The functional-equation fold (A1-c, item 3).** Parametric in the half-box count
(`hfin`, `hhalf`): the full strip-box count is at most twice the half-box bound. The low box
folds into the high box at ordinate `−t` (multiplicity preserved, `zeta_analyticOrderAt_one_sub`),
and `log(|−t|+2) = log(|t|+2)`; the seam `Re = 1/2` is inside `[1/2,1)`, so `(0,1/2) ⊔ [1/2,1)`
partitions `(0,1)` with no double count. -/
theorem zeta_box_count_full {C : ℝ}
    (hfin : ∀ u : ℝ, (zBoxHi u).Finite)
    (hhalf : ∀ u : ℝ, zBoxCount (zBoxHi u) ≤ C * Real.log (|u| + 2)) (t : ℝ) :
    zBoxCount (zBoxFull t) ≤ 2 * C * Real.log (|t| + 2) := by
  -- the reflection `σ = (1 - ·)` and its landing
  set σ : ℂ → ℂ := fun ρ => 1 - ρ with hσ
  have hinj : Set.InjOn σ (zBoxLo t) := fun a _ b _ h => by simpa [hσ, sub_right_inj] using h
  have himg : σ '' zBoxLo t ⊆ zBoxHi (-t) := by
    rintro w ⟨ρ, hρ, rfl⟩
    obtain ⟨hz, hρ0, hρhalf, hw⟩ := hρ
    refine ⟨(zeta_zero_one_sub_iff hρ0 (by linarith)).mpr hz, ?_, ?_, ?_⟩
    · rw [hσ]; simp only [Complex.sub_re, Complex.one_re]; linarith
    · rw [hσ]; simp only [Complex.sub_re, Complex.one_re]; linarith
    · rw [hσ]; simp only [Complex.sub_im, Complex.one_im]
      rw [show (0 : ℝ) - ρ.im - -t = -(ρ.im - t) by ring, abs_neg]; exact hw
  -- the low box is finite (injects into the finite high box at `−t`)
  have himgfin : (σ '' zBoxLo t).Finite := (hfin (-t)).subset himg
  have hlofin : (zBoxLo t).Finite := Set.Finite.of_finite_image himgfin hinj
  -- the fold: count(lo) = count(σ ''lo) ≤ count(hi at −t)
  have heq : zBoxCount (σ '' zBoxLo t) = zBoxCount (zBoxLo t) := by
    simp only [zBoxCount, finsum_mem_image hinj]
    refine finsum_mem_congr rfl ?_
    intro ρ hρ
    obtain ⟨_, hρ0, hρhalf, _⟩ := hρ
    simp only [hσ, zZeroMult]
    rw [zeta_analyticOrderAt_one_sub hρ0 (by linarith)]
  have hlo_le : zBoxCount (zBoxLo t) ≤ zBoxCount (zBoxHi (-t)) := by
    rw [← heq]; exact zBoxCount_mono himg (hfin (-t))
  -- the partition `full = lo ⊔ hi`
  have hunion : zBoxFull t = zBoxLo t ∪ zBoxHi t := by
    ext ρ
    simp only [zBoxFull, zBoxLo, zBoxHi, Set.mem_setOf_eq, Set.mem_union]
    constructor
    · rintro ⟨hz, hg0, hg1, hw⟩
      rcases lt_or_ge ρ.re (1 / 2) with h | h
      · exact Or.inl ⟨hz, hg0, h, hw⟩
      · exact Or.inr ⟨hz, h, hg1, hw⟩
    · rintro (⟨hz, hg0, h, hw⟩ | ⟨hz, h, hg1, hw⟩)
      · exact ⟨hz, hg0, by linarith, hw⟩
      · exact ⟨hz, by linarith, hg1, hw⟩
  have hdisj : Disjoint (zBoxLo t) (zBoxHi t) := by
    rw [Set.disjoint_left]
    rintro ρ ⟨_, _, hlt, _⟩ ⟨_, hge, _, _⟩
    linarith
  have hsum : zBoxCount (zBoxFull t) = zBoxCount (zBoxLo t) + zBoxCount (zBoxHi t) := by
    simp only [zBoxCount, hunion]
    exact finsum_mem_union hdisj hlofin (hfin t)
  -- assemble: each half `≤ C·log(|t|+2)`
  have hlo : zBoxCount (zBoxLo t) ≤ C * Real.log (|t| + 2) :=
    hlo_le.trans (by have := hhalf (-t); rwa [abs_neg] at this)
  rw [hsum, show (2 : ℝ) * C * Real.log (|t| + 2)
    = C * Real.log (|t| + 2) + C * Real.log (|t| + 2) by ring]
  exact add_le_add hlo (hhalf t)

end Salt.SW

end




section
open Complex Filter Topology

theorem solution {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    analyticOrderAt riemannZeta (1 - ρ) = analyticOrderAt riemannZeta ρ := by
  apply Salt.SW.zeta_analyticOrderAt_one_sub <;> assumption

end

