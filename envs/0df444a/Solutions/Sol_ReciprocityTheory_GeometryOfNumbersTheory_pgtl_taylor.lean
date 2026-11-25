-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.pgtl_taylor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:01:30.255008+00:00
-- url     : https://prove2.me/submissions/6fe47e5d-ba6d-40b1-a2bd-def62d08c033

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_TaylorLeviSt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Complex
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution {D : ℕ} {ρ₀ K₃ : ℝ} (φ : (Fin D → ℂ) → ℝ)
    (hφ : ContDiffOn ℝ 3 φ (Metric.ball 0 ρ₀))
    (hK₃ : ∀ z ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, ‖iteratedFDeriv ℝ 3 φ z‖ ≤ K₃)
    (z : Fin D → ℂ) (hz : z ∈ Metric.ball (0 : Fin D → ℂ) ρ₀) :
    |φ z - φ 0 - fderiv ℝ φ 0 z - fderiv ℝ (fderiv ℝ φ) 0 z z / 2| ≤ K₃ * ‖z‖ ^ 3 := by
  have hzr : ‖z‖ < ρ₀ := mem_ball_zero_iff.mp hz
  have h0 : (0 : Fin D → ℂ) ∈ Metric.ball (0 : Fin D → ℂ) ρ₀ :=
    Metric.mem_ball_self ((norm_nonneg z).trans_lt hzr)
  have hK : 0 ≤ K₃ := (norm_nonneg _).trans (hK₃ 0 h0)
  have hat : ∀ x ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, ContDiffAt ℝ 3 φ x :=
    fun x hx => hφ.contDiffAt (Metric.isOpen_ball.mem_nhds hx)
  set B := fderiv ℝ (fderiv ℝ φ) 0 with hB
  set d₁ := fderiv ℝ φ 0 with hd₁
  set s := Metric.closedBall (0 : Fin D → ℂ) ‖z‖ with hs
  have hsub : s ⊆ Metric.ball 0 ρ₀ := Metric.closedBall_subset_ball hzr
  have hsc : Convex ℝ s := convex_closedBall _ _
  have h0s : (0 : Fin D → ℂ) ∈ s := Metric.mem_closedBall_self (norm_nonneg z)
  have hzs : z ∈ s := mem_closedBall_zero_iff.2 le_rfl
  have hxs : ∀ x ∈ s, ‖x‖ ≤ ‖z‖ := fun x hx => mem_closedBall_zero_iff.1 hx
  have hd3 : ∀ x ∈ s, HasFDerivAt (fderiv ℝ (fderiv ℝ φ))
      (fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) x) x := by
    intro x hx
    have h2 := ((hat x (hsub hx)).fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1)
      (by norm_num)
    exact (h2.differentiableAt (by norm_num)).hasFDerivAt
  have hd2 : ∀ x ∈ s, HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) x) x := by
    intro x hx
    have h2 := (hat x (hsub hx)).fderiv_right (m := 2) (by norm_num)
    exact (h2.differentiableAt (by norm_num)).hasFDerivAt
  have hd1 : ∀ x ∈ s, HasFDerivAt φ (fderiv ℝ φ x) x := by
    intro x hx
    exact ((hat x (hsub hx)).differentiableAt (by norm_num)).hasFDerivAt
  have hT : ∀ x ∈ s, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) x‖ ≤ K₃ := by
    intro x hx
    have e : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) x‖ = ‖iteratedFDeriv ℝ 3 φ x‖ := by
      rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := fderiv ℝ (fderiv ℝ (fderiv ℝ φ))),
        norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_fderiv]
    rw [e]; exact hK₃ x (hsub hx)
  have hA : ∀ x ∈ s, ‖fderiv ℝ (fderiv ℝ φ) x - B‖ ≤ K₃ * ‖x‖ := by
    intro x hx
    have := hsc.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun y hy => (hd3 y hy).hasFDerivWithinAt) hT h0s hx
    simpa using this
  have hBd : ∀ x ∈ s, HasFDerivAt (fun y => fderiv ℝ φ y - d₁ - B y)
      (fderiv ℝ (fderiv ℝ φ) x - B) x := by
    intro x hx
    exact ((hd2 x hx).sub_const d₁).sub B.hasFDerivAt
  have hBb : ∀ x ∈ s, ‖fderiv ℝ (fderiv ℝ φ) x - B‖ ≤ K₃ * ‖z‖ :=
    fun x hx => (hA x hx).trans (mul_le_mul_of_nonneg_left (hxs x hx) hK)
  have hψ : ∀ x ∈ s, ‖fderiv ℝ φ x - d₁ - B x‖ ≤ K₃ * ‖z‖ * ‖x‖ := by
    intro x hx
    have := hsc.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun y hy => (hBd y hy).hasFDerivWithinAt) hBb h0s hx
    simpa [hd₁] using this
  have hsym : ∀ v w, B v w = B w v := (hat 0 h0).isSymmSndFDerivAt (by simp; norm_num)
  have hCd : ∀ x ∈ s, HasFDerivAt (fun y => φ y - φ 0 - d₁ y - B y y / 2)
      (fderiv ℝ φ x - d₁ - B x) x := by
    intro x hx
    have h := ((((hd1 x hx).sub_const (φ 0)).sub d₁.hasFDerivAt).sub
      (HasFDerivAt.mul_const (B.hasFDerivAt.clm_apply (hasFDerivAt_id x)) (2⁻¹ : ℝ)))
    have hf : (fun y => φ y - φ 0 - d₁ y - B y y / 2) =
        ((fun x => φ x - φ 0) - ⇑d₁ - fun y => (B y) (id y) * 2⁻¹) := by
      funext y; simp [div_eq_mul_inv]
    rw [hf]
    refine h.congr_fderiv ?_
    ext h'
    simp
    rw [hsym h' x]
    ring
  have hCb : ∀ x ∈ s, ‖fderiv ℝ φ x - d₁ - B x‖ ≤ K₃ * ‖z‖ * ‖z‖ :=
    fun x hx => (hψ x hx).trans (mul_le_mul_of_nonneg_left (hxs x hx) (by positivity))
  have key := hsc.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun y hy => (hCd y hy).hasFDerivWithinAt) hCb h0s hzs
  simp only [sub_self, map_zero, zero_div, sub_zero,
    Real.norm_eq_abs] at key
  calc _ ≤ K₃ * ‖z‖ * ‖z‖ * ‖z‖ := key
    _ = K₃ * ‖z‖ ^ 3 := by ring
end ReciprocityTheory.GeometryOfNumbersTheory
