-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KTheta_integral_exp_qf_b8e3fb58d743
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:38:09.779812+00:00
-- url     : https://prove2.me/submissions/4b9712b7-2067-4014-a8d5-e7a5974402cc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_NormInvSmulMemSphere
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ThetaGauss
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KTheta_qf_star_mul_self_975fe84e53ae
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KTheta_integral_exp_sum_sq_107f6dbe98ea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KTheta_integral_comp_mulVec_d6bc6b3375ff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Matrix MeasureTheory Real
open scoped MatrixOrder
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.KTheta
noncomputable section
variable {g : ℕ}
namespace GroundTheory.Heights₂.Heights.KTheta
theorem _root_.solution (Y : Matrix (Fin g) (Fin g) ℝ) (hY : Y.PosDef) (c : ℝ) :
    ∫ v, exp (-c * qf Y v) = (√(π / c)) ^ g * (√Y.det)⁻¹ := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hY.posSemidef.nonneg
  have hdetY : Y.det = B.det ^ 2 := by
    rw [hB, det_mul, star_eq_conjTranspose, det_conjTranspose]; simp [sq]
  have hBdet : B.det ≠ 0 := by
    intro h; have := hY.det_pos; rw [hdetY, h] at this; simp at this
  calc ∫ v, exp (-c * qf Y v) = ∫ v, (fun x : Fin g → ℝ => exp (-c * ∑ i, x i ^ 2)) (B *ᵥ v) := by
        congr 1; funext v; rw [hB, qf_star_mul_self]
    _ = |B.det|⁻¹ * ∫ x : Fin g → ℝ, exp (-c * ∑ i, x i ^ 2) :=
        integral_comp_mulVec B hBdet (fun x : Fin g → ℝ => exp (-c * ∑ i, x i ^ 2)) (by fun_prop)
    _ = (√(π / c)) ^ g * (√Y.det)⁻¹ := by
        rw [integral_exp_sum_sq c, hdetY, Real.sqrt_sq_eq_abs]; ring
end GroundTheory.Heights₂.Heights.KTheta
