-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_X_sub_C_9853297c8fca
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:06.712018+00:00
-- url     : https://prove2.me/submissions/7bde963d-200d-4259-a66f-e8c460ad6789

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GradientAtPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_apply_6330d6b8766e

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
theorem _root_.solution [DecidableEq σ] (j : σ) : grad w (X j - C (w j)) = Pi.single j 1 := by
  ext i
  rw [grad_apply, map_sub, pderiv_C, sub_zero, pderiv_X]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]
end GroundTheory.Heights₂.Heights.GradientAtPoint
