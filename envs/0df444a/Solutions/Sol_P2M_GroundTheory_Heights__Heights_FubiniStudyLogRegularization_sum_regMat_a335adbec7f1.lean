-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_sum_regMat_a335adbec7f1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:56.480801+00:00
-- url     : https://prove2.me/submissions/7ade093a-e06e-4a45-a837-2ca5c1c357d0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PFsLogSmul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_FsLogRegBasic

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
open Matrix MeasureTheory
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.FubiniStudyLogRegularization
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.FubiniStudyLogRegularization
theorem _root_.solution (h : HermNorm n) (u : Fin n → ℂ) {ε : ℝ} (hε : 0 ≤ ε) (y : Fin n → ℂ) :
    ∑ i, ‖(regMat h u ε *ᵥ y) i‖ ^ 2 = ‖∑ j, u j * y j‖ ^ 2 + ε * sqDual h y := by
  have h0 : (regMat h u ε *ᵥ y) 0 = ∑ j, u j * y j := by
    simp [regMat, Matrix.mulVec, dotProduct]
  rw [Fin.sum_univ_succ, sqDual, Finset.mul_sum, h0, add_right_inj]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (regMat h u ε *ᵥ y) i.succ = ((√ε : ℝ) : ℂ) * ((h.matᵀ)⁻¹ *ᵥ y) i := by
    simp only [regMat, Matrix.mulVec, dotProduct, Matrix.of_apply, Fin.cons_succ, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum, mul_assoc]
  rw [this, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hε]
end GroundTheory.Heights₂.Heights.FubiniStudyLogRegularization
