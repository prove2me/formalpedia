-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_BlowUpHorizontalStrict_full_af2ac8f6ec68
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:04:13.046409+00:00
-- url     : https://prove2.me/submissions/ac4a1648-0a42-498e-8fc1-2eb36e509055

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpHorizontal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LiftFormNotMemBlowUpOf
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpHorizontalStrict
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUpOf_mono_79a813d4a6e9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUpOf_isPrime_f9d5f4560679
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUpOf_comap_le_1f0469125f95
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_le_and_isRelevant_of_divCycle_ne_zero_6b368bc3dee6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_mem_blowUpOf_d5667072f554


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
noncomputable section
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace BlowUpHorizontalStrict
theorem _root_.solution : BlowUpHorizontalStrict.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hex hloc c x hx hxP W hW hϖW hj
  obtain ⟨j₀, hj₀⟩ := hj
  obtain ⟨hWp, hBW, -⟩ := le_and_isRelevant_of_divCycle_ne_zero hW
  have hmin : W ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes := by
    unfold divCycle at hW
    split_ifs at hW with h
    · exact h.1
    · exact absurd rfl hW
  have hPW₀ : P ≤ W.comap (liftForm (ι := ι) (J := J) (R := O)) := fun p hp => hBW (liftForm_mem_blowUpOf hp)
  have hle := blowUpOf_comap_le hWp hBW hj₀
  have hxW : liftForm x ∈ W := hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  refine le_antisymm (hmin.2 ⟨blowUpOf_isPrime (Ideal.comap_isPrime _ _) u,
    sup_le (blowUpOf_mono hPW₀ u) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)⟩ hle) hle
  exact liftForm_mem_blowUpOf (P := W.comap (liftForm (ι := ι) (J := J) (R := O))) hxW
end BlowUpHorizontalStrict
end GroundTheory.Heights₂.Heights.NumbersDVR
