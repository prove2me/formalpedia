-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GradientAtPoint_sub_C_eval_mem_span_40e355beff8a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:30:34.582489+00:00
-- url     : https://prove2.me/submissions/c5b34d2b-977d-4ce3-ad44-7a4b2a860425

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GradientAtPoint

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
theorem _root_.solution (p : MvPolynomial σ ℂ) :
    p - C (eval w p) ∈ Ideal.span (Set.range fun i => (X i - C (w i) : MvPolynomial σ ℂ)) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    rw [map_add, map_add, show p + q - (C (eval w p) + C (eval w q)) = (p - C (eval w p)) + (q - C (eval w q)) by
      ring]
    exact Ideal.add_mem _ hp hq
  | mul_X p i hp =>
    rw [map_mul, eval_X, map_mul,
      show p * X i - C (eval w p) * C (w i) = (p - C (eval w p)) * X i + C (eval w p) * (X i - C (w i)) by ring]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hp)
      (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩))
end GroundTheory.Heights₂.Heights.GradientAtPoint
