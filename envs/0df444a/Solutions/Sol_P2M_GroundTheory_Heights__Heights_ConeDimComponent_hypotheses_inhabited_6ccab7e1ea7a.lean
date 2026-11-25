-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeDimComponent_hypotheses_inhabited_6ccab7e1ea7a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:33:24.596862+00:00
-- url     : https://prove2.me/submissions/190ac8b5-0223-4a2f-8eb3-c297150f54d5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ringKrullDim_quot_bot_acd27392687d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_span_X_zero_mem_relComps_0c705e008944

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
namespace GroundTheory.Heights₂.Heights
namespace ConeDimComponent
theorem _root_.solution :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧
      ringKrullDim (MvPolynomial (Fin 2) ℚ ⧸ (⊥ : Ideal (MvPolynomial (Fin 2) ℚ))) =
        ((1 + 1 : ℕ) : WithBot ℕ∞) ∧
      linForm (fun j : Fin 2 => if j = 0 then (1 : ℚ) else 0) ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧
      Ideal.span {X 0} ∈ relComps ((⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ⊔
        Ideal.span {linForm (fun j : Fin 2 => if j = 0 then (1 : ℚ) else 0)}) := by
  refine ⟨⟨Ideal.isPrime_bot, fun f hf d => ?_, ⟨0, ?_⟩⟩, ringKrullDim_quot_bot ℚ 2, ?_,
    span_X_zero_mem_relComps ℚ⟩
  · rw [Ideal.mem_bot] at hf ⊢; simp [hf]
  · rw [Ideal.mem_bot]; exact X_ne_zero 0
  · rw [Ideal.mem_bot]; simp [linForm, X_ne_zero]
end ConeDimComponent
end GroundTheory.Heights₂.Heights
