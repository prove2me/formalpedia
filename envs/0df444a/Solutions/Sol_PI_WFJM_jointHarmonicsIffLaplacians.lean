-- Prove2me | solution 1 for PI.WFJM.jointHarmonicsIffLaplacians
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:58:53.255122+00:00
-- url     : https://prove2.me/submissions/0c37e89d-9c82-44f8-8ceb-9b8cc9ec421c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Theorems.Thm_PI_WFJM_loweringPart_leftAction_inl_inr
import Theorems.Thm_PI_WFJM_loweringPart_leftAction_inr_inl
import Theorems.Thm_PI_WFJM_loweringPart_rightAction_inl_inr
import Theorems.Thm_PI_WFJM_loweringPart_rightAction_inr_inl
import Theorems.Thm_PI_WFJM_minusPart1_expand
import Theorems.Thm_PI_WFJM_minusPart2_expand
import Theorems.Thm_PI_WFJM_isPC_Eab

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.WFJM
open MvPolynomial
open PI.FJM
namespace PI.WFJM
theorem _root_.solution : FormJ := by
  intro p q r s P
  simp only [FockH1Action.Jset, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hL, hR⟩
    refine ⟨fun i j => ?_, fun i j => ?_, fun k l => ?_, fun k l => ?_⟩
    · have h := hL _ (isPC_Eab (Sum.inl i) (Sum.inr j)
        (by simp [FockH1Action.sameBlock]))
      rw [loweringPart_leftAction_inl_inr] at h
      exact neg_eq_zero.mp h
    · have h := hL _ (isPC_Eab (Sum.inr j) (Sum.inl i)
        (by simp [FockH1Action.sameBlock]))
      rw [loweringPart_leftAction_inr_inl] at h
      exact neg_eq_zero.mp h
    · have h := hR _ (isPC_Eab (Sum.inr l) (Sum.inl k)
        (by simp [FockH1Action.sameBlock]))
      rw [loweringPart_rightAction_inr_inl] at h
      exact neg_eq_zero.mp h
    · have h := hR _ (isPC_Eab (Sum.inl k) (Sum.inr l)
        (by simp [FockH1Action.sameBlock]))
      rw [loweringPart_rightAction_inl_inr] at h
      exact neg_eq_zero.mp h
  · rintro ⟨hA, hB, hC, hD⟩
    refine ⟨fun X hX => ?_, fun Y hY => ?_⟩
    · rw [minusPart1_expand]
      refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
      rcases a with i | j <;> rcases b with i' | j'
      · rw [hX (Sum.inl i) (Sum.inl i') (by simp [FockH1Action.sameBlock]), zero_smul]
      · rw [loweringPart_leftAction_inl_inr, hA, neg_zero, smul_zero]
      · rw [loweringPart_leftAction_inr_inl, hB, neg_zero, smul_zero]
      · rw [hX (Sum.inr j) (Sum.inr j') (by simp [FockH1Action.sameBlock]), zero_smul]
    · rw [minusPart2_expand]
      refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
      rcases c with k | l <;> rcases d with k' | l'
      · rw [hY (Sum.inl k) (Sum.inl k') (by simp [FockH1Action.sameBlock]), zero_smul]
      · rw [loweringPart_rightAction_inl_inr, hD, neg_zero, smul_zero]
      · rw [loweringPart_rightAction_inr_inl, hC, neg_zero, smul_zero]
      · rw [hY (Sum.inr l) (Sum.inr l') (by simp [FockH1Action.sameBlock]), zero_smul]
end PI.WFJM
