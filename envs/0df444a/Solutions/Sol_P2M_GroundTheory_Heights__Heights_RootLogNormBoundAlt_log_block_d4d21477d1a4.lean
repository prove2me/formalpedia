-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RootLogNormBoundAlt_log_block_d4d21477d1a4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:26.727887+00:00
-- url     : https://prove2.me/submissions/4c8e16b9-2a2d-4b3b-96f2-259081d624d5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootLogNormBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootLogNormBoundAlt_norm_block_le_93e0782b40a7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.RootLogNormBoundAlt
namespace GroundTheory.Heights₂.Heights.RootLogNormBoundAlt
theorem _root_.solution (h₃ : PlueckerKernel.Statement) (j m : ℕ) (Z : Matrix (Fin j) (Fin m) ℂ)
    (hZ : ∀ a b, ‖Z a b‖ = 1) (a : ℂ) (ha : a ≠ 0) (v : PlIdx j m → ℂ)
    (hv : ∀ I, v I = a * (colsOf (onePipe Z) I).det) (hv0 : 0 < ‖WithLp.toLp 2 v‖) :
    -((j : ℝ) / 2 * Real.log (1 + m)) ≤ Real.log (‖a‖ / ‖WithLp.toLp 2 v‖) := by
  have hb := norm_block_le h₃ j m Z hZ a v hv
  have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hm : (0 : ℝ) < (1 + m : ℝ) ^ j := by positivity
  have hl := Real.log_le_log hv0 hb
  rw [Real.log_mul ha'.ne' (Real.sqrt_pos.mpr hm).ne', Real.log_sqrt hm.le, Real.log_pow] at hl
  rw [Real.log_div ha'.ne' hv0.ne']
  linarith
end GroundTheory.Heights₂.Heights.RootLogNormBoundAlt
