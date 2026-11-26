-- Prove2me | solution 1 for TunnellMap.OrthogonalFrame.affine_norm_root_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:58:24.508146+00:00
-- url     : https://prove2.me/submissions/23addeaf-7171-4943-ac6b-ac1a1920aa98

import Definitions.Def_TunnellMap_ShortInterval
import Definitions.Def_TunnellMap_QuadraticRoots
import Theorems.Thm_TunnellMap_quadraticEquation_iff_root_certificate
import Theorems.Thm_TunnellMap_OrthogonalFrame_affine_norm_eq_iff
import Theorems.Thm_TunnellMap_OrthogonalFrame_affineQuadratic_discriminant
import Theorems.Thm_TunnellMap_OrthogonalFrame_det_eq_one
import Theorems.Thm_TunnellMap_dot_tau
import Theorems.Thm_TunnellMap_evenEquiv_apply
import Theorems.Thm_TunnellMap_evenEquiv_symm_apply
import Theorems.Thm_TunnellMap_qForm_aLift
import Theorems.Thm_TunnellMap_qForm_bLift
import Theorems.Thm_TunnellMap_qForm_tau
attribute [local simp] TunnellMap.dot_tau
attribute [local simp] TunnellMap.evenEquiv_apply
attribute [local simp] TunnellMap.evenEquiv_symm_apply
attribute [local simp] TunnellMap.qForm_aLift
attribute [local simp] TunnellMap.qForm_bLift
attribute [local simp] TunnellMap.qForm_tau



set_option autoImplicit true
open TunnellMap
open TunnellMap.OrthogonalFrame
variable {p : Triple} (F : OrthogonalFrame p)
namespace TunnellMap.OrthogonalFrame
theorem _root_.solution (A q a b : ℤ) :
    dot (linComb3 a b (q * A) F.e₁ F.e₂ F.z)
        (linComb3 a b (q * A) F.e₁ F.e₂ F.z) = A ↔
      ∃ u : ℤ,
        u ^ 2 = F.halfDiscriminant A q b ∧
        dot F.e₁ F.e₁ * a =
          -(dot F.e₁ F.e₂ * b + q * A * dot F.z F.e₁) + u := by
  rw [F.affine_norm_eq_iff]
  have hquad : F.affineQuadratic A q a b = 0 ↔
      quadraticEquation (dot F.e₁ F.e₁)
        (dot F.e₁ F.e₂ * b + q * A * dot F.z F.e₁)
        (dot F.e₂ F.e₂ * b ^ 2 +
          2 * (q * A) * dot F.z F.e₂ * b +
          (q * A) ^ 2 * dot F.z F.z - A) a := by
    unfold affineQuadratic quadraticEquation
    constructor <;> intro h <;> nlinarith
  rw [hquad]
  have hα : dot F.e₁ F.e₁ ≠ 0 := by
    intro hzero
    have hx : F.e₁.x = 0 := by
      simp [dot] at hzero
      nlinarith [sq_nonneg F.e₁.y, sq_nonneg F.e₁.z]
    have hy : F.e₁.y = 0 := by
      simp [dot] at hzero
      nlinarith [sq_nonneg F.e₁.x, sq_nonneg F.e₁.z]
    have hz : F.e₁.z = 0 := by
      simp [dot] at hzero
      nlinarith [sq_nonneg F.e₁.x, sq_nonneg F.e₁.y]
    have hdet := F.det_eq_one
    simp [det3, cross, dot, hx, hy, hz] at hdet
  rw [quadraticEquation_iff_root_certificate hα]
  rw [F.affineQuadratic_discriminant]
end TunnellMap.OrthogonalFrame
