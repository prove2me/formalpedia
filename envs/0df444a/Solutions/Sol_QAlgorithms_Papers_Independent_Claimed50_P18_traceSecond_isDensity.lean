-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P18.traceSecond_isDensity
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-03T22:22:37.537905+00:00
-- url     : https://prove2.me/submissions/49f07d22-e4b2-49f2-8e25-d45adcb9fffd

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P18

noncomputable section

open Filter

open scoped ENNReal BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Frontier18.P01

open QAlgorithms.Papers.Independent.Frontier18.P08 (operatorTrace)

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Claimed50.P18

/-- Squared ℓ² norm as a series. -/
theorem ptd_sq {K E : Type} [NormedAddCommGroup E] (v : lp (fun _ : K => E) 2) :
    Summable (fun k => ‖v k‖ ^ 2) ∧ ‖v‖ ^ 2 = ∑' k, ‖v k‖ ^ 2 := by
  have h1 := Memℓp.summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (lp.memℓp v)
  have h2 := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) v
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h1 h2
  exact ⟨h1, h2⟩

/-- The slice `i ↦ u (i, j)` of a vector in `ℓ²(I × J)`. -/
def ptdSlice {I J : Type} (u : Hilbert (I × J)) (j : J) : Hilbert I :=
  ⟨fun i => u (i, j), memℓp_gen (by
    have h : Summable (fun i => ‖u (i, j)‖ ^ 2) := (ptd_sq u).1.comp_injective
      (show Function.Injective (fun i : I => (i, j)) from fun a b h => by simpa using h)
    simpa [ENNReal.toReal_ofNat, Real.rpow_two] using h)⟩

theorem ptd_slice_apply {I J : Type} (u : Hilbert (I × J)) (j : J) (i : I) :
    (ptdSlice u j : I → ℂ) i = u (i, j) := rfl

theorem ptd_slice_sq {I J : Type} (u : Hilbert (I × J)) :
    Summable (fun j => ‖ptdSlice u j‖ ^ 2) ∧ ∑' j, ‖ptdSlice u j‖ ^ 2 = ‖u‖ ^ 2 := by
  have hs := (ptd_sq u).1
  have hfib : ∀ j, ‖ptdSlice u j‖ ^ 2 = ∑' i, ‖u (i, j)‖ ^ 2 := fun j => (ptd_sq (ptdSlice u j)).2
  simp_rw [hfib]
  refine ⟨by simpa using hs.prod_symm.prod, ?_⟩
  rw [(ptd_sq u).2, hs.tsum_prod]
  exact Summable.tsum_comm (f := fun i j => ‖u (i, j)‖ ^ 2) hs

/-- The ℓ²(J) vector of slice norms. -/
def ptdNorms {I J : Type} (u : Hilbert (I × J)) : lp (fun _ : J => ℝ) 2 :=
  ⟨fun j => ‖ptdSlice u j‖, memℓp_gen (by simpa [Real.rpow_two] using (ptd_slice_sq u).1)⟩

theorem ptd_norms_norm {I J : Type} (u : Hilbert (I × J)) : ‖ptdNorms u‖ = ‖u‖ := by
  have h := (ptd_sq (ptdNorms u)).2
  have h' : ∑' j, ‖(ptdNorms u : J → ℝ) j‖ ^ 2 = ‖u‖ ^ 2 := by
    simpa [ptdNorms] using (ptd_slice_sq u).2
  rw [h'] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

/-- Cauchy–Schwarz over the slices. -/
theorem ptd_cs {I J : Type} (l r : Hilbert (I × J)) :
    Summable (fun j => ‖ptdSlice l j‖ * ‖ptdSlice r j‖) ∧
      ∑' j, ‖ptdSlice l j‖ * ‖ptdSlice r j‖ ≤ ‖l‖ * ‖r‖ := by
  have hin : ∀ x y : ℝ, inner ℝ x y = x * y := by intro x y; simp [mul_comm]
  have hs := lp.summable_inner (𝕜 := ℝ) (ptdNorms l) (ptdNorms r)
  have he := lp.inner_eq_tsum (𝕜 := ℝ) (ptdNorms l) (ptdNorms r)
  simp only [hin] at hs he
  refine ⟨hs, ?_⟩
  have := real_inner_le_norm (ptdNorms l) (ptdNorms r)
  rw [he, ptd_norms_norm, ptd_norms_norm] at this
  exact this

theorem ptd_trace_class {I J : Type} [Countable J] (X : Matrix (I × J) (I × J) ℂ)
    (e : NuclearExpansion X) :
    (∀ i i', Summable (fun j => X (i, j) (i', j))) ∧ IsTraceClass (traceSecond X) := by
  have hg : Summable (fun p : ℕ × J =>
      ‖ptdSlice (e.left p.1) p.2‖ * ‖ptdSlice (e.right p.1) p.2‖) := by
    refine (summable_prod_of_nonneg (fun p => mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
      ⟨fun n => (ptd_cs (e.left n) (e.right n)).1, ?_⟩
    exact Summable.of_nonneg_of_le
      (fun n => tsum_nonneg fun j => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun n => (ptd_cs (e.left n) (e.right n)).2) e.summable
  have hF : ∀ i i', Summable (fun p : ℕ × J => e.left p.1 (i, p.2) * star (e.right p.1 (i', p.2))) := by
    intro i i'
    refine Summable.of_norm_bounded hg fun p => ?_
    rw [norm_mul, norm_star]
    exact mul_le_mul (lp.norm_apply_le_norm (by norm_num) (ptdSlice (e.left p.1) p.2) i)
      (lp.norm_apply_le_norm (by norm_num) (ptdSlice (e.right p.1) p.2) i')
      (norm_nonneg _) (norm_nonneg _)
  have hX : ∀ i i' j, X (i, j) (i', j) =
      ∑' n, e.left n (i, j) * star (e.right n (i', j)) := fun i i' j => e.coefficients _ _
  have hrow : ∀ i i', Summable (fun j => X (i, j) (i', j)) := by
    intro i i'
    simp only [hX]
    simpa using (hF i i').prod_symm.prod
  refine ⟨hrow, ?_⟩
  obtain ⟨φ, hφ⟩ := exists_injective_nat (ℕ × J)
  let L : ℕ → Hilbert I := Function.extend φ (fun p => ptdSlice (e.left p.1) p.2) 0
  let R : ℕ → Hilbert I := Function.extend φ (fun p => ptdSlice (e.right p.1) p.2) 0
  have hL : ∀ p, L (φ p) = ptdSlice (e.left p.1) p.2 := hφ.extend_apply _ _
  have hR : ∀ p, R (φ p) = ptdSlice (e.right p.1) p.2 := hφ.extend_apply _ _
  have hL0 : ∀ k, k ∉ Set.range φ → L k = 0 := fun k hk => Function.extend_apply' _ _ _ hk
  have hR0 : ∀ k, k ∉ Set.range φ → R k = 0 := fun k hk => Function.extend_apply' _ _ _ hk
  refine ⟨{ left := L, right := R, summable := ?_, coefficients := ?_ }⟩
  · refine (hφ.summable_iff fun k hk => by simp [hL0 k hk]).1 ?_
    convert hg using 1
    funext p
    simp [Function.comp, hL, hR]
  · intro i i'
    have hsupp : Function.support (fun k => (L k : I → ℂ) i * star ((R k : I → ℂ) i')) ⊆
        Set.range φ := by
      intro k hk
      by_contra hn
      apply hk
      simp [hL0 k hn]
    rw [← hφ.tsum_eq hsupp]
    simp only [hL, hR, ptd_slice_apply]
    change ∑' j, X (i, j) (i', j) = _
    simp only [hX]
    rw [Summable.tsum_comm (f := fun n j => e.left n (i, j) * star (e.right n (i', j))) (hF i i'),
      ← (hF i i').tsum_prod]

theorem ptd_main {I J : Type} [Countable I] [Countable J] (rho : State (I × J)) :
    IsDensity (traceSecond rho.coefficients) := by
  obtain ⟨⟨e⟩, hpos, hds, hdsum⟩ := rho.density
  set X := rho.coefficients
  obtain ⟨hrow, htc⟩ := ptd_trace_class X e
  refine ⟨htc, ?_, ?_, ?_⟩
  · intro s z
    let q : J → ℂ := fun j => ∑ i ∈ s, ∑ i' ∈ s, star (z i) * X (i, j) (i', j) * z i'
    have hterm : ∀ i i', Summable (fun j => star (z i) * X (i, j) (i', j) * z i') :=
      fun i i' => ((hrow i i').mul_left _).mul_right _
    have hqs : Summable q := summable_sum fun i _ => summable_sum fun i' _ => hterm i i'
    have hQ : (∑ i ∈ s, ∑ i' ∈ s, star (z i) * traceSecond X i i' * z i') = ∑' j, q j := by
      rw [Summable.tsum_finsetSum (fun i _ => summable_sum fun i' _ => hterm i i')]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Summable.tsum_finsetSum (fun i' _ => hterm i i')]
      refine Finset.sum_congr rfl fun i' _ => ?_
      simp only [traceSecond]
      rw [← tsum_mul_left, ← tsum_mul_right]
    have hq : ∀ j, (q j).im = 0 ∧ 0 ≤ (q j).re := by
      intro j
      have := hpos (s ×ˢ {j}) (fun p => z p.1)
      simpa [q, Finset.sum_product] using this
    rw [hQ, Complex.im_tsum hqs, Complex.re_tsum hqs]
    exact ⟨by simp [fun j => (hq j).1], tsum_nonneg fun j => (hq j).2⟩
  · have hre : ∀ i, (traceSecond X i i).re = ∑' j, (X (i, j) (i, j)).re :=
      fun i => Complex.re_tsum (hrow i i)
    simp only [hre]
    simpa using hds.prod
  · have hre : ∀ i, (traceSecond X i i).re = ∑' j, (X (i, j) (i, j)).re :=
      fun i => Complex.re_tsum (hrow i i)
    simp only [hre]
    rw [← hds.tsum_prod (f := fun p => (X p p).re)]
    exact hdsum

end QAlgorithms.Papers.Independent.Claimed50.P18

open QAlgorithms.Papers.Independent.Claimed50.P18 in
theorem solution {I J : Type} [Countable I] [Countable J] (rho : State (I × J)) :
    IsDensity (traceSecond rho.coefficients) :=
  ptd_main rho
