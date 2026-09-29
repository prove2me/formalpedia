-- Prove2me | solution 1 for OnlineConvexOpt.SecondOrder.exp_concave_quadratic_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:57:23.841259+00:00
-- url     : https://prove2.me/submissions/a035648b-292a-4f24-9786-c5f8b159e4f6

import Mathlib
import Definitions.Def_OnlineConvexOpt_SecondOrder_ExpConcave

open OnlineConvexOpt.SecondOrder


namespace OnlineConvexOpt.SecondOrder

theorem qlb_logm_deriv (t : ℝ) (ht : t < 1) :
    HasDerivAt (fun t : ℝ => -t - t ^ 2 / 4 - Real.log (1 - t)) (t * (1 + t) / (2 * (1 - t))) t := by
  have hne : (1 - t) ≠ 0 := by linarith
  have h := (((hasDerivAt_id t).neg).sub ((hasDerivAt_pow 2 t).div_const 4)).sub
    (((hasDerivAt_id t).const_sub 1).log hne)
  refine h.congr_deriv ?_
  simp only [id]
  field_simp
  ring

theorem qlb_log_bound (z : ℝ) (hz1 : -1 ≤ z) (hz2 : z < 1) :
    Real.log (1 - z) ≤ -z - z ^ 2 / 4 := by
  let m : ℝ → ℝ := fun t => -t - t ^ 2 / 4 - Real.log (1 - t)
  have m0 : m 0 = 0 := by simp [m]
  suffices 0 ≤ m z by simp only [m] at this; linarith
  rcases le_or_gt 0 z with h0 | h0
  · have hmono : MonotoneOn m (Set.Icc 0 z) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 z)
        (f' := fun t => t * (1 + t) / (2 * (1 - t)))
      · intro t ht; exact (qlb_logm_deriv t (by linarith [ht.2])).continuousAt.continuousWithinAt
      · intro t ht; rw [interior_Icc] at ht
        exact (qlb_logm_deriv t (by linarith [ht.2])).hasDerivWithinAt
      · intro t ht; rw [interior_Icc] at ht
        have : 0 < 1 - t := by linarith [ht.2]
        apply div_nonneg <;> nlinarith [ht.1]
    have := hmono ⟨le_rfl, h0⟩ ⟨h0, le_rfl⟩ h0
    linarith
  · have hanti : AntitoneOn m (Set.Icc z 0) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc z 0)
        (f' := fun t => t * (1 + t) / (2 * (1 - t)))
      · intro t ht; exact (qlb_logm_deriv t (by linarith [ht.2])).continuousAt.continuousWithinAt
      · intro t ht; rw [interior_Icc] at ht
        exact (qlb_logm_deriv t (by linarith [ht.2])).hasDerivWithinAt
      · intro t ht; rw [interior_Icc] at ht
        have : 0 < 2 * (1 - t) := by linarith [ht.2]
        apply div_nonpos_of_nonpos_of_nonneg _ this.le
        nlinarith [ht.1, ht.2]
    have := hanti ⟨le_rfl, h0.le⟩ ⟨h0.le, le_rfl⟩ h0.le
    linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem qlb_fderiv_ineq (K : Set E) (F : E → ℝ) (hF : ConvexOn ℝ K F) (x y : E)
    (hx : x ∈ K) (hy : y ∈ K) (L : E →L[ℝ] ℝ) (hL : HasFDerivAt F L y) :
    F y + L (x - y) ≤ F x := by
  let φ : ℝ → ℝ := fun t => F (y + t • (x - y))
  have hmem : ∀ t ∈ Set.Icc (0:ℝ) 1, y + t • (x - y) ∈ K :=
    fun t ht => hF.1.add_smul_sub_mem hy hx ht
  have hφ : ConvexOn ℝ (Set.Icc (0:ℝ) 1) φ := by
    refine ⟨convex_Icc 0 1, fun s hs t ht a b ha hb hab => ?_⟩
    have h := hF.2 (hmem s hs) (hmem t ht) ha hb hab
    have heq : y + (a • s + b • t) • (x - y) = a • (y + s • (x - y)) + b • (y + t • (x - y)) := by
      rw [show b = 1 - a by linarith]; simp only [smul_eq_mul]; module
    simp only [φ]
    rw [heq]; exact h
  have hd : HasDerivAt φ (L (x - y)) 0 := by
    have hl : HasDerivAt (fun t : ℝ => y + t • (x - y)) ((1:ℝ) • (x - y)) 0 :=
      ((hasDerivAt_id (0:ℝ)).smul_const (x - y)).const_add y
    have := hL.comp_hasDerivAt_of_eq (0:ℝ) hl (by simp)
    rw [one_smul] at this
    exact this
  have := hφ.le_slope_of_hasDerivAt ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_lt_one hd
  simp [slope_def_field, φ] at this
  have := L.map_sub x y
  linarith

theorem qlb_core (α D G γ : ℝ) (K : Set E) (f : E → ℝ)
    (hf : IsExpConcaveOn α K f) (hD : ∀ p ∈ K, ∀ q ∈ K, dist p q ≤ D)
    (hG : ∀ p ∈ K, ∀ v, HasGradientAt f v p → ‖v‖ ≤ G)
    (hγ : γ ≤ (1 / 2) * min (1 / (G * D)) α)
    (x y : E) (hx : x ∈ K) (hy : y ∈ K) (g : E) (hg : HasGradientAt f g y) :
    f y + inner ℝ g (x - y) + (γ / 2) * (inner ℝ g (x - y)) ^ 2 ≤ f x := by
  have hfd : HasFDerivAt f (InnerProductSpace.toDual ℝ E g) y := hg.hasFDerivAt
  set s := inner ℝ g (x - y) with hs
  rcases le_or_gt γ 0 with hγ0 | hγ0
  · have h1 := qlb_fderiv_ineq K f hf.1 x y hx hy _ hfd
    simp only [InnerProductSpace.toDual_apply_apply] at h1
    have : (γ / 2) * s ^ 2 ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
    linarith
  -- positive γ
  have hmin : 2 * γ ≤ min (1 / (G * D)) α := by linarith
  have hα : 2 * γ ≤ α := hmin.trans (min_le_right _ _)
  have hGD' : 2 * γ ≤ 1 / (G * D) := hmin.trans (min_le_left _ _)
  have hGDpos : 0 < G * D := by
    have : 0 < 1 / (G * D) := by linarith
    exact one_div_pos.mp this
  have hαpos : 0 < α := by linarith
  have hgG : ‖g‖ ≤ G := hG y hy g hg
  have hxy : ‖x - y‖ ≤ D := by rw [← dist_eq_norm]; exact hD x hx y hy
  have hsabs : |s| ≤ G * D := by
    calc |s| ≤ ‖g‖ * ‖x - y‖ := abs_real_inner_le_norm _ _
      _ ≤ G * D := mul_le_mul hgG hxy (norm_nonneg _) ((norm_nonneg _).trans hgG)
  have h2γGD : 2 * γ * (G * D) ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hGD' hGDpos.le
    rwa [one_div, inv_mul_cancel₀ hGDpos.ne'] at this
  -- tangent inequality for -exp(-α f)
  have hFd : HasFDerivAt (fun z => -Real.exp (-α * f z))
      (-(Real.exp (-α * f y) • ((-α) • InnerProductSpace.toDual ℝ E g))) y :=
    ((hfd.const_mul (-α)).exp).neg
  have h1 := qlb_fderiv_ineq K _ hf.2.neg x y hx hy _ hFd
  simp only [Pi.neg_apply, ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
    InnerProductSpace.toDual_apply_apply, smul_eq_mul] at h1
  rw [← hs] at h1
  set u := f x - f y with hu
  have hE0 : 0 < Real.exp (-α * f y) := Real.exp_pos _
  have hsplit : Real.exp (-α * f x) = Real.exp (-α * f y) * Real.exp (-α * u) := by
    rw [← Real.exp_add]; congr 1; rw [hu]; ring
  have hkey : Real.exp (-α * u) ≤ 1 - α * s := by
    rw [hsplit] at h1
    have : Real.exp (-α * f y) * Real.exp (-α * u) ≤ Real.exp (-α * f y) * (1 - α * s) := by
      nlinarith
    exact le_of_mul_le_mul_left this hE0
  have hpos1 : 0 < 1 - α * s := lt_of_lt_of_le (Real.exp_pos _) hkey
  set β := 2 * γ with hβ
  have hβpos : 0 < β := by linarith
  set p := β / α with hp
  have hp0 : 0 ≤ p := div_nonneg hβpos.le hαpos.le
  have hp1 : p ≤ 1 := (div_le_one hαpos).mpr hα
  have hexpβ : Real.exp (-β * u) = Real.exp (-α * u) ^ p := by
    rw [← Real.exp_mul]; congr 1; rw [hp]; field_simp
  have hb1 : Real.exp (-β * u) ≤ 1 - β * s := by
    rw [hexpβ]
    calc Real.exp (-α * u) ^ p ≤ (1 - α * s) ^ p :=
          Real.rpow_le_rpow (Real.exp_pos _).le hkey hp0
      _ = (1 + (-(α * s))) ^ p := by ring_nf
      _ ≤ 1 + p * (-(α * s)) := rpow_one_add_le_one_add_mul_self (by linarith) hp0 hp1
      _ = 1 - β * s := by rw [hp]; field_simp; ring
  have hz1 : -1 ≤ β * s := by
    have := neg_abs_le s
    nlinarith
  have hz2 : β * s < 1 := by
    have := Real.exp_pos (-β * u); linarith
  have hlog := qlb_log_bound (β * s) hz1 hz2
  have hle : -β * u ≤ Real.log (1 - β * s) := by
    rw [Real.le_log_iff_exp_le (by linarith)]; exact hb1
  have hfin : β * (s + (γ / 2) * s ^ 2) ≤ β * u := by
    rw [hβ] at hlog hle ⊢; nlinarith
  have := le_of_mul_le_mul_left hfin hβpos
  rw [hu] at this
  linarith

end OnlineConvexOpt.SecondOrder

open OnlineConvexOpt.SecondOrder


theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (α D G γ : ℝ) (K : Set E) (f : E → ℝ)
    (hf : IsExpConcaveOn α K f) (hD : ∀ p ∈ K, ∀ q ∈ K, dist p q ≤ D)
    (hG : ∀ p ∈ K, ∀ v, HasGradientAt f v p → ‖v‖ ≤ G)
    (hγ : γ ≤ (1 / 2) * min (1 / (G * D)) α)
    (x y : E) (hx : x ∈ K) (hy : y ∈ K) (g : E) (hg : HasGradientAt f g y) :
    f y + inner ℝ g (x - y) + (γ / 2) * (inner ℝ g (x - y)) ^ 2 ≤ f x := by
  exact qlb_core α D G γ K f hf hD hG hγ x y hx hy g hg
