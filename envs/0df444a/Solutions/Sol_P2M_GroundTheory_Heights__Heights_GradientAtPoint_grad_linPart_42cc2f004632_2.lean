-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_linPart_42cc2f004632
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:55:59.245355+00:00
-- url     : https://prove2.me/submissions/3125086a-b835-418f-a956-3ee3824ea5db

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GradientAtPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_mul_206fa499c46e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_C_e893e68d7bf6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_X_sub_C_9853297c8fca

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.GradientAtPoint
variable {σ : Type*} (w : σ → ℂ)
namespace GroundTheory.Heights₂.Heights.GradientAtPoint
theorem _root_.solution [Fintype σ] (c : σ → ℂ) : grad w (linPart w c) = c := by
  classical
  ext i
  rw [linPart, map_sum, Finset.sum_apply]
  simp [grad_mul, grad_C, grad_X_sub_C, Pi.single_apply]
end GroundTheory.Heights₂.Heights.GradientAtPoint
