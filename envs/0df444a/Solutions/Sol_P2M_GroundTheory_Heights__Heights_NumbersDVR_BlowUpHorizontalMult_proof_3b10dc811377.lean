-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_BlowUpHorizontalMult_proof_3b10dc811377
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:04:07.247297+00:00
-- url     : https://prove2.me/submissions/b100fe6c-b647-476f-a9dc-306ab7ba26db

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpHorizontalMult
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LiftFormNotMemBlowUpOf
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPolynomialLocalizedLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpHorizontalMult
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_PolynomialLocalizedLength_full_3abcc90ed158
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_comap_liftForm_facts_3c10203679d9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_le_and_isRelevant_of_divCycle_ne_zero_6b368bc3dee6


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
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace BlowUpHorizontalMult
theorem _root_.solution (hmin : BlowUpHorizontalMinimal.Statement.{u})
    (hchart : BlowUpHorizontalChartLength.Statement.{u}) : BlowUpHorizontalMult.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hex hloc c x hx hxP W hW hϖW
  have hm := hmin O ϖ hϖ K ι J P n hP N u hu hex hloc c x hx hxP W hW hϖW
  obtain ⟨hWp, hBW, hrel⟩ := le_and_isRelevant_of_divCycle_ne_zero hW
  obtain ⟨-, -, hrel₀, -⟩ := comap_liftForm_facts hWp hBW hrel
  have hcond : W ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes ∧ IsRelevant W := by
    by_contra h
    unfold divCycle at hW
    rw [dif_neg h] at hW
    exact hW rfl
  have hch := hchart O ϖ hϖ K ι J P n hP N u hu hex hloc c x hx hxP W hW hϖW hWp
  have := hWp
  have hp := PolynomialLocalizedLength.full (MRing ι O) (W.comap (liftForm (ι := ι) (J := J) (R := O))) (P ⊔ Ideal.span {x})
  unfold divCycle
  rw [dif_pos ⟨hm, hrel₀⟩, dif_pos hcond]
  congr 2
  exact (hp.symm.trans hch.symm : _)
end BlowUpHorizontalMult
end GroundTheory.Heights₂.Heights.NumbersDVR
