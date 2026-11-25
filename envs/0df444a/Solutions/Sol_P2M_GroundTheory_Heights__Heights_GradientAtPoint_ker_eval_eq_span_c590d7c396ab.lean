-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GradientAtPoint_ker_eval_eq_span_c590d7c396ab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:08:23.028292+00:00
-- url     : https://prove2.me/submissions/8ff3cc88-926e-4a3c-a3ed-48ee521f0ce8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GradientAtPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradientAtPoint_sub_C_eval_mem_span_40e355beff8a

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
theorem _root_.solution :
    RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ) =
      Ideal.span (Set.range fun i => (X i - C (w i) : MvPolynomial σ ℂ)) := by
  apply le_antisymm
  · intro p hp
    have h := sub_C_eval_mem_span w p
    rwa [RingHom.mem_ker.1 hp, map_zero, sub_zero] at h
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp [RingHom.mem_ker]
end GroundTheory.Heights₂.Heights.GradientAtPoint
