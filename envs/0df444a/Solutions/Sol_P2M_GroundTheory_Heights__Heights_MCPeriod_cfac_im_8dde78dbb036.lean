-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCPeriod_cfac_im_8dde78dbb036
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:18:11.24716+00:00
-- url     : https://prove2.me/submissions/7d82b555-907c-4b06-a9d8-a4fff0906af4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Period

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCPeriod
open Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights.MCPeriod
theorem _root_.solution (l : ℂ) :
    (l / (2 * Real.pi * Complex.I)).im = (2 * Real.pi)⁻¹ * Real.log ‖Complex.exp l‖⁻¹ := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 : l / (2 * Real.pi * Complex.I) = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * (-Complex.I * l) := by
    push_cast
    field_simp
    have := Complex.I_mul_I
    linear_combination l * this
  rw [h1, Complex.im_ofReal_mul, Complex.norm_exp, Real.log_inv, Real.log_exp]
  simp
end GroundTheory.Heights₂.Heights.MCPeriod
