-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KTheta_integral_exp_two_pi_qf_7f0897f8e415
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:22:50.276396+00:00
-- url     : https://prove2.me/submissions/8304ab9b-0495-45e9-bc47-4af5c09aa623

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_NormInvSmulMemSphere
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ThetaGauss
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KTheta_integral_exp_qf_b8e3fb58d743

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
theorem _root_.solution (Y : Matrix (Fin g) (Fin g) ℝ) (hY : Y.PosDef) :
    ∫ v, exp (-(2 * π) * qf Y v) = ((2 : ℝ) ^ g * Y.det) ^ (-(1 / 2 : ℝ)) := by
  rw [integral_exp_qf Y hY (2 * π)]
  have hd := hY.det_pos
  have h2 : π / (2 * π) = (2 : ℝ)⁻¹ := by field_simp
  rw [h2, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_mul (by positivity),
    Real.sqrt_inv, mul_inv, inv_pow]
  congr 1
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), mul_comm]
end GroundTheory.Heights₂.Heights.KTheta
