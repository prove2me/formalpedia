-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_mul_of_eval_eq_zero_a46392587438
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:18.893518+00:00
-- url     : https://prove2.me/submissions/b64f1993-da0a-4eb4-b9f3-d7df37c2d178

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GradientAtPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_mul_206fa499c46e

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
theorem _root_.solution (r p : MvPolynomial σ ℂ) (hp : eval w p = 0) :
    grad w (r * p) = eval w r • grad w p := by
  rw [grad_mul, hp, zero_smul, add_zero]
end GroundTheory.Heights₂.Heights.GradientAtPoint
