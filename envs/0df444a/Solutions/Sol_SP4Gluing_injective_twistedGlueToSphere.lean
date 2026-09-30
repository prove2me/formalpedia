-- Prove2me | solution 1 for SP4Gluing.injective_twistedGlueToSphere
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T01:44:35.637715+00:00
-- url     : https://prove2.me/submissions/73aa847c-0622-4b01-bccb-e2d2e46c4d1d

import Mathlib
import Definitions.Def_SP4Gluing

set_option autoImplicit false
open Set Metric SP4Gluing SPC4Disk

namespace InjAux

variable {m : ℕ}

/-- The first coordinate of a point of the upper hemisphere, read off the disk chart. -/
lemma upper_coord_zero (w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    (upperHemisphereHomeoDisk.symm w).val.val 0 = Real.sqrt (1 - ‖w.val‖ ^ 2) := rfl

/-- The first coordinate of a point of the lower hemisphere: the reflected chart flips the sign. -/
lemma lower_coord_zero (v : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    (lowerHemisphereHomeoDiskRefl.symm v).val.val 0 = -Real.sqrt (1 - ‖v.val‖ ^ 2) := rfl

/-- The lower chart is the reflection of the upper one. -/
lemma lower_eq_reflect (v : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    (lowerHemisphereHomeoDiskRefl.symm v).val.val
      = reflectFirst (upperHemisphereHomeoDisk.symm v).val.val := rfl

/-- A chart point sits on the equator exactly when its disk coordinate is on the boundary. -/
lemma norm_eq_one_of_sqrt_eq_zero (w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (h : Real.sqrt (1 - ‖w.val‖ ^ 2) = 0) : ‖w.val‖ = 1 := by
  have hle : ‖w.val‖ ≤ 1 := mem_closedBall_zero_iff.mp w.2
  have hnn : (0 : ℝ) ≤ 1 - ‖w.val‖ ^ 2 := by nlinarith [norm_nonneg w.val]
  have h0 : 1 - ‖w.val‖ ^ 2 = 0 := by
    have := Real.sqrt_eq_zero hnn |>.mp h
    exact this
  nlinarith [norm_nonneg w.val]

/-- `alexanderExt` preserves the radius exactly; this is what makes the trick work. -/
lemma alexanderExt_norm
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    ‖(alexanderExt φ w).val‖ = ‖w.val‖ := by
  show ‖‖w.val‖ • (φ (unitOr diskNorth w.val)).val‖ = ‖w.val‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    mem_sphere_zero_iff_norm.mp (φ (unitOr diskNorth w.val)).2, mul_one]

/-- The Alexander extension of `φ` is inverted by that of `φ.symm`. -/
theorem alexanderExt_leftInverse
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    alexanderExt φ.symm (alexanderExt φ w) = w := by
  apply Subtype.ext
  by_cases h : w.val = 0
  · have h1 : (alexanderExt φ w).val = 0 := by
      show ‖w.val‖ • (φ (unitOr diskNorth w.val)).val = 0
      rw [h, norm_zero, zero_smul]
    show ‖(alexanderExt φ w).val‖ • (φ.symm (unitOr diskNorth (alexanderExt φ w).val)).val
      = w.val
    rw [h1, norm_zero, zero_smul, h]
  · set r : ℝ := ‖w.val‖ with hr
    have hrpos : 0 < r := norm_pos_iff.mpr h
    set u : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 := unitOr diskNorth w.val with hu
    have hval : (alexanderExt φ w).val = r • (φ u).val := rfl
    have hnorm : ‖(alexanderExt φ w).val‖ = r := by
      rw [hval, norm_smul, Real.norm_eq_abs, abs_of_nonneg hrpos.le,
        mem_sphere_zero_iff_norm.mp (φ u).2, mul_one]
    have hunit : unitOr diskNorth (alexanderExt φ w).val = φ u := by
      rw [hval]; exact unitOr_smul diskNorth hrpos (φ u)
    show ‖(alexanderExt φ w).val‖ • (φ.symm (unitOr diskNorth (alexanderExt φ w).val)).val
      = w.val
    rw [hnorm, hunit, Homeomorph.symm_apply_apply, hu, smul_unitOr diskNorth h]

lemma alexanderExt_injective
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    Function.Injective (alexanderExt φ) :=
  Function.LeftInverse.injective (alexanderExt_leftInverse φ)

end InjAux

open InjAux

theorem solution {m : ℕ}
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    Function.Injective (twistedGlueToSphere φ) := by
  -- the equatorial identification, extracted once and used in both mixed cases
  have key : ∀ (w₁ w₂ : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1),
      (upperHemisphereHomeoDisk.symm w₁).val
        = (lowerHemisphereHomeoDiskRefl.symm (alexanderExt φ.symm w₂)).val →
      Quot.mk (GlueRel φ) (Sum.inl w₁) = Quot.mk (GlueRel φ) (Sum.inr w₂) := by
    intro w₁ w₂ hab
    set v := alexanderExt φ.symm w₂ with hv
    -- read off the first coordinate: nonnegative on one side, nonpositive on the other
    have hcoord : Real.sqrt (1 - ‖w₁.val‖ ^ 2) = -Real.sqrt (1 - ‖v.val‖ ^ 2) := by
      have := congrArg (fun x : EuclideanSpace ℝ (Fin (m + 2)) => x 0) (congrArg Subtype.val hab)
      simpa [upper_coord_zero, lower_coord_zero] using this
    have h1 : Real.sqrt (1 - ‖w₁.val‖ ^ 2) = 0 := by
      have a1 := Real.sqrt_nonneg (1 - ‖w₁.val‖ ^ 2)
      have a2 := Real.sqrt_nonneg (1 - ‖v.val‖ ^ 2)
      linarith
    have h2 : Real.sqrt (1 - ‖v.val‖ ^ 2) = 0 := by linarith
    have hn1 : ‖w₁.val‖ = 1 := norm_eq_one_of_sqrt_eq_zero w₁ h1
    have hnv : ‖v.val‖ = 1 := norm_eq_one_of_sqrt_eq_zero v h2
    have hn2 : ‖w₂.val‖ = 1 := by rw [← alexanderExt_norm φ.symm w₂, ← hv]; exact hnv
    -- both disk points are on the boundary sphere
    set u : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 :=
      ⟨w₁.val, mem_sphere_zero_iff_norm.mpr hn1⟩ with hu
    set u₂ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 :=
      ⟨w₂.val, mem_sphere_zero_iff_norm.mpr hn2⟩ with hu₂
    have hw₁ : w₁ = sphereToDisk u := Subtype.ext rfl
    have hw₂ : w₂ = sphereToDisk u₂ := Subtype.ext rfl
    have hvval : v = sphereToDisk (φ.symm u₂) := by
      rw [hv, hw₂, alexanderExt_sphereToDisk]
    -- on the equator the reflection is the identity, so the two charts agree
    have hrefl : (lowerHemisphereHomeoDiskRefl.symm v).val.val
        = (upperHemisphereHomeoDisk.symm v).val.val := by
      rw [lower_eq_reflect]
      refine reflectFirst_eq_self_of_coord_zero _ ?_
      rw [upper_coord_zero, h2]
    have hcharts : upperHemisphereHomeoDisk.symm w₁ = upperHemisphereHomeoDisk.symm v := by
      apply Subtype.ext; apply Subtype.ext
      rw [← hrefl, ← congrArg Subtype.val hab]
    have hdisk : w₁ = v := upperHemisphereHomeoDisk.symm.injective hcharts
    have huu : u = φ.symm u₂ := by
      apply Subtype.ext
      have := congrArg Subtype.val hdisk
      rw [hvval] at this
      exact this
    have hu₂eq : u₂ = φ u := by rw [huu, Homeomorph.apply_symm_apply]
    rw [hw₁, hw₂, hu₂eq]
    exact Quot.sound (GlueRel.glue u)
  intro a b hab
  induction a using Quot.ind with
  | _ a =>
  induction b using Quot.ind with
  | _ b =>
  match a, b with
  | Sum.inl w₁, Sum.inl w₂ =>
      have hval : (upperHemisphereHomeoDisk.symm w₁).val
          = (upperHemisphereHomeoDisk.symm w₂).val := hab
      rw [upperHemisphereHomeoDisk.symm.injective (Subtype.ext hval)]
  | Sum.inr w₁, Sum.inr w₂ =>
      have hval : (lowerHemisphereHomeoDiskRefl.symm (alexanderExt φ.symm w₁)).val
          = (lowerHemisphereHomeoDiskRefl.symm (alexanderExt φ.symm w₂)).val := hab
      have h2 := lowerHemisphereHomeoDiskRefl.symm.injective (Subtype.ext hval)
      rw [alexanderExt_injective φ.symm h2]
  | Sum.inl w₁, Sum.inr w₂ => exact key w₁ w₂ hab
  | Sum.inr w₁, Sum.inl w₂ => exact (key w₂ w₁ hab.symm).symm
