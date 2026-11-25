-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GradientAtPoint_sub_linPart_mem_sq_27d5d7fbb6f3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:46:31.403484+00:00
-- url     : https://prove2.me/submissions/08c68f2c-98c9-416c-b0ae-4c9a1ead1520

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GradientAtPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_mul_206fa499c46e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_X_sub_C_9853297c8fca
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradientAtPoint_ker_eval_eq_span_c590d7c396ab

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
    (hp : p ∈ RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)) :
    p - linPart w (grad w p) ∈ RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ) ^ 2 := by
  classical
  rw [ker_eval_eq_span] at hp
  obtain ⟨a, rfl⟩ := (Ideal.mem_span_range_iff_exists_fun).1 hp
  have hg : grad w (∑ i, a i * (X i - C (w i))) = fun i => eval w (a i) := by
    rw [map_sum]
    simp_rw [grad_mul, grad_X_sub_C, map_sub, eval_X, eval_C, sub_self, zero_smul, add_zero]
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hg, linPart, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [← sub_mul, pow_two]
  refine Ideal.mul_mem_mul ?_ ?_
  · simp [RingHom.mem_ker]
  · simp [RingHom.mem_ker]
end GroundTheory.Heights₂.Heights.GradientAtPoint
