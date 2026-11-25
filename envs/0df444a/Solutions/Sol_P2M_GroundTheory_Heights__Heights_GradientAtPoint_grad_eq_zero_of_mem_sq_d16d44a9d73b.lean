-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_eq_zero_of_mem_sq_d16d44a9d73b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:30:28.143577+00:00
-- url     : https://prove2.me/submissions/1f6c7d9e-2319-4b4c-a902-b6a26fe26bac

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
theorem _root_.solution {p : MvPolynomial σ ℂ}
    (hp : p ∈ RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ) ^ 2) : grad w p = 0 := by
  rw [pow_two] at hp
  refine Submodule.mul_induction_on hp (fun a ha b hb => ?_) (fun x y hx hy => ?_)
  · rw [grad_mul, RingHom.mem_ker.1 ha, RingHom.mem_ker.1 hb, zero_smul, zero_smul, add_zero]
  · rw [map_add, hx, hy, add_zero]
end GroundTheory.Heights₂.Heights.GradientAtPoint
