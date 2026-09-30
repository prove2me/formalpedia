-- Prove2me | solution 1 for SP4Gluing.twistedSphere_homeomorphic
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T01:36:35.772028+00:00
-- url     : https://prove2.me/submissions/71a0e438-edaf-42a8-b2d9-d01f1bdac8a7

import Mathlib
import Definitions.Def_SP4Gluing
import Theorems.Thm_SP4Gluing_continuous_twistedGlueToSphere
import Theorems.Thm_SP4Gluing_injective_twistedGlueToSphere

set_option autoImplicit false
open Set Metric SP4Gluing SPC4Disk

namespace AlexAux

variable {m : ℕ}

/-- The Alexander extension of `φ` is inverted by the Alexander extension of `φ.symm`. -/
theorem alexanderExt_leftInverse
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    alexanderExt φ.symm (alexanderExt φ w) = w := by
  apply Subtype.ext
  by_cases h : w.val = 0
  · -- the centre is fixed: the radial factor kills everything
    have h1 : (alexanderExt φ w).val = 0 := by
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


/-- The mirror statement, with the roles of `φ` and `φ.symm` exchanged. -/
theorem alexanderExt_rightInverse
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    alexanderExt φ (alexanderExt φ.symm w) = w := by
  have h := alexanderExt_leftInverse φ.symm w
  rwa [Homeomorph.symm_symm] at h

/-- The glue map onto the sphere is surjective: each hemisphere is hit by one disk. -/
theorem surjective_twistedGlueToSphere
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    Function.Surjective (twistedGlueToSphere φ) := by
  intro x
  rcases le_total 0 (x.val 0) with h | h
  · refine ⟨Quot.mk _ (Sum.inl (upperHemisphereHomeoDisk ⟨x, h⟩)), ?_⟩
    show (upperHemisphereHomeoDisk.symm (upperHemisphereHomeoDisk ⟨x, h⟩)).val = x
    rw [Homeomorph.symm_apply_apply]
  · refine ⟨Quot.mk _ (Sum.inr (alexanderExt φ (lowerHemisphereHomeoDiskRefl ⟨x, h⟩))), ?_⟩
    show (lowerHemisphereHomeoDiskRefl.symm
      (alexanderExt φ.symm (alexanderExt φ (lowerHemisphereHomeoDiskRefl ⟨x, h⟩)))).val = x
    rw [alexanderExt_leftInverse, Homeomorph.symm_apply_apply]

end AlexAux

open AlexAux

theorem solution {m : ℕ}
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    Nonempty (TwistedSphere φ ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (m + 2))) 1) := by
  have hbij : Function.Bijective (twistedGlueToSphere φ) :=
    ⟨SP4Gluing.injective_twistedGlueToSphere φ, surjective_twistedGlueToSphere φ⟩
  exact ⟨(SP4Gluing.continuous_twistedGlueToSphere φ).homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ hbij)⟩
