-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GradientAtPoint_mem_sq_of_grad_eq_zero_7cd8970785ba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:56:37.90543+00:00
-- url     : https://prove2.me/submissions/4d536bbd-5ba1-4ed0-922e-e94c99b5affd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GradientAtPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradientAtPoint_sub_linPart_mem_sq_27d5d7fbb6f3

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
theorem _root_.solution [Fintype σ] {p : MvPolynomial σ ℂ}
    (hp : p ∈ RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)) (hg : grad w p = 0) :
    p ∈ RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ) ^ 2 := by
  have h := sub_linPart_mem_sq w hp
  rwa [hg, linPart, Finset.sum_eq_zero (fun i _ => by simp), sub_zero] at h
end GroundTheory.Heights₂.Heights.GradientAtPoint
