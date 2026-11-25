-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_height_ker_eval_line_99b464f3247b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:31:48.967655+00:00
-- url     : https://prove2.me/submissions/19643b3f-55df-4ba1-8529-e6368ef96b2b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationLength

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
open MvPolynomial ComplexSets
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution : (RingHom.ker (eval (0 : Fin 1 → ℂ))).height = 1 := by
  apply le_antisymm
  · have h := Ideal.height_le_ringKrullDim_of_ne_top
      (I := RingHom.ker (eval (0 : Fin 1 → ℂ))) (RingHom.ker_ne_top _)
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
      Nat.card_eq_fintype_card, Fintype.card_fin] at h
    exact_mod_cast h
  · rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    intro h
    have hX : (X 0 : MvPolynomial (Fin 1) ℂ) ∈ RingHom.ker (eval (0 : Fin 1 → ℂ)) := by simp
    rw [h, Ideal.mem_bot] at hX
    exact X_ne_zero _ hX
end GroundTheory.Heights₂.Heights
