-- Prove2me | solution 1 for RelaxedPRS.BestIter.theorem_A_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T18:59:02.493525+00:00
-- url     : https://prove2.me/submissions/e852fa44-2bed-4acf-ad4f-0517e53410c2

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_RelaxedPRS_BestIter_Setting
open ThreeOpSplitting.ConvexRates MoreauProx.Characterization Filter

namespace Aux_RPRS_A1

open InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma descent (f : H → ℝ) (g : H → H) (hd : ∀ z, HasFDerivAt f (toDual ℝ H (g z)) z) (L : ℝ)
    (hS : ∀ a b : H, ‖g a - g b‖ ≤ L * ‖a - b‖) (x z : H) :
    f z ≤ f x + inner ℝ (g x) (z - x) + L / 2 * ‖z - x‖ ^ 2 := by
  set v := z - x with hv
  set c := inner ℝ (g x) v with hc
  let ψ : ℝ → ℝ := fun t => f (x + t • v) - t * c - L / 2 * t ^ 2 * ‖v‖ ^ 2
  have hderiv : ∀ t, HasDerivAt ψ (inner ℝ (g (x + t • v)) v - c - L * t * ‖v‖ ^ 2) t := by
    intro t
    have hline : HasDerivAt (fun s : ℝ => x + s • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add x
    have h1 := (hd (x + t • v)).comp_hasDerivAt t hline
    rw [toDual_apply_apply] at h1
    have h2 : HasDerivAt (fun s : ℝ => s * c) c t := by
      simpa using (hasDerivAt_id t).mul_const c
    have h3 : HasDerivAt (fun s : ℝ => L / 2 * s ^ 2 * ‖v‖ ^ 2) (L * t * ‖v‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖v‖ ^ 2)
      refine this.congr_deriv ?_
      rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
      push_cast
      ring
    exact (h1.sub h2).sub h3
  have hanti : AntitoneOn ψ (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact fun t _ => (hderiv t).continuousAt.continuousWithinAt
    · exact fun t _ => (hderiv t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hderiv t).deriv]
      have hL := hS (x + t • v) x
      have hn : ‖x + t • v - x‖ = t * ‖v‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1.le]
      have hi : inner ℝ (g (x + t • v)) v - c ≤ ‖g (x + t • v) - g x‖ * ‖v‖ := by
        rw [hc, ← inner_sub_left]
        exact real_inner_le_norm _ _
      rw [hn] at hL
      nlinarith [norm_nonneg v, mul_le_mul_of_nonneg_right hL (norm_nonneg v)]
  have h := hanti ⟨le_refl 0, zero_le_one⟩ ⟨zero_le_one, le_refl 1⟩ zero_le_one
  have e1 : x + (1 : ℝ) • v = z := by rw [one_smul, hv, add_sub_cancel]
  have e0 : x + (0 : ℝ) • v = x := by rw [zero_smul, add_zero]
  simp only [ψ, e1, e0] at h
  norm_num at h
  linarith

lemma first_order (f : H → ℝ) (hc : ConvexOn ℝ Set.univ f) (x : H) (g : H)
    (hd : HasFDerivAt f (toDual ℝ H g) x) (y : H) :
    f x + inner ℝ g (y - x) ≤ f y := by
  have hφ : ConvexOn ℝ Set.univ (f ∘ (AffineMap.lineMap x y : ℝ →ᵃ[ℝ] H)) := by
    simpa using hc.comp_affineMap (AffineMap.lineMap x y : ℝ →ᵃ[ℝ] H)
  have hder : HasDerivAt (f ∘ (AffineMap.lineMap x y : ℝ →ᵃ[ℝ] H)) (toDual ℝ H g (y - x)) 0 :=
    hd.comp_hasDerivAt_of_eq (0 : ℝ) AffineMap.hasDerivAt_lineMap (by simp)
  have := hφ.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hder
  rw [slope_def_field] at this
  simp only [Function.comp_apply, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one,
    sub_zero, div_one, toDual_apply_apply] at this
  linarith

end Aux_RPRS_A1

open ThreeOpSplitting.ConvexRates MoreauProx.Characterization Aux_RPRS_A1 InnerProductSpace in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (h : H → ℝ) (β : ℝ) (hβ : 0 < β) (hh : IsSmoothConvex β h) :
    (∀ x y : H, h x ≤ h y + inner ℝ (x - y) (gradient h y) + 1 / (2 * β) * ‖x - y‖ ^ 2) ∧
    (∀ x y : H, β * ‖gradient h x - gradient h y‖ ^ 2 ≤
      inner ℝ (x - y) (gradient h x - gradient h y)) := by
  obtain ⟨hcv, hdf, hL⟩ := hh
  have hd : ∀ z, HasFDerivAt h (toDual ℝ H (gradient h z)) z := fun z =>
    hasGradientAt_iff_hasFDerivAt.mp (hdf z).hasGradientAt
  refine ⟨fun x y => ?_, fun x y => ?_⟩
  · have := descent h (gradient h) hd β⁻¹ hL y x
    rw [real_inner_comm]
    have e : 1 / (2 * β) = β⁻¹ / 2 := by ring
    rw [e]; exact this
  · -- key inequality: h x + ⟪∇x, y - x⟫ + β/2 ‖∇y - ∇x‖² ≤ h y
    have key : ∀ x y : H, h x + inner ℝ (gradient h x) (y - x) +
        β / 2 * ‖gradient h y - gradient h x‖ ^ 2 ≤ h y := by
      intro x y
      set a := gradient h x with ha
      let φ : H → ℝ := fun z => h z - toDual ℝ H a z
      have hdφ : ∀ z, HasFDerivAt φ (toDual ℝ H (gradient h z - a)) z := by
        intro z
        have := (hd z).sub (toDual ℝ H a).hasFDerivAt
        rw [← map_sub] at this
        exact this
      have hLφ : ∀ u w : H, ‖(gradient h u - a) - (gradient h w - a)‖ ≤ β⁻¹ * ‖u - w‖ := by
        intro u w; rw [sub_sub_sub_cancel_right]; exact hL u w
      set G := gradient h y - a with hG
      have hdes := descent φ (fun z => gradient h z - a) hdφ β⁻¹ hLφ y (y - β • G)
      have hmin := first_order h hcv x a (hd x) (y - β • G)
      simp only [φ, toDual_apply_apply, sub_sub_cancel_left, inner_neg_right, inner_smul_right,
        norm_neg, norm_smul, Real.norm_of_nonneg hβ.le, real_inner_self_eq_norm_sq] at hdes
      rw [← hG] at hdes
      rw [inner_sub_right] at hmin
      have e : β⁻¹ / 2 * (β * ‖G‖) ^ 2 = β / 2 * ‖G‖ ^ 2 := by
        field_simp
      rw [e] at hdes
      rw [inner_sub_right]
      have := real_inner_self_eq_norm_sq G
      nlinarith
    have k1 := key x y
    have k2 := key y x
    rw [norm_sub_rev] at k1
    have e : inner ℝ (x - y) (gradient h x - gradient h y) =
        -(inner ℝ (gradient h x) (y - x) + inner ℝ (gradient h y) (x - y)) := by
      rw [← neg_sub x y, inner_neg_right, inner_sub_right, real_inner_comm (x - y),
        real_inner_comm (x - y)]
      ring
    rw [e]
    linarith
