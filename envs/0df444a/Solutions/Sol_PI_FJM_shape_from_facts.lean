-- Prove2me | solution 1 for PI.FJM.shape_from_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:31:01.159885+00:00
-- url     : https://prove2.me/submissions/0d1c677f-daf6-48f7-96a1-c55f368308e3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeFromFacts
import Theorems.Thm_PI_WFJM_Shape_length_lpos
import Theorems.Thm_PI_WFJM_Shape_length_lneg
import Theorems.Thm_PI_WFJM_Shape_nP_add_nN_le
import Theorems.Thm_PI_WFJM_Shape_eq_pad
import Theorems.Thm_P2M_PI_WFJM_Shape_pos_of__P_7e79a0d73165
import Theorems.Thm_P2M_PI_WFJM_Shape_pos_of__N_cf6537b449c1
import Theorems.Thm_PI_WFJM_Shape_lpos_eq_of_sq
import Theorems.Thm_PI_WFJM_Shape_lneg_eq_of_sq
import Theorems.Thm_PI_WFJM_Shape_pairwise_lpos
import Theorems.Thm_PI_WFJM_Shape_pairwise_lneg

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
open PI PI.FJM
open PI.WFJM.Shape
namespace PI.FJM
theorem _root_.solution : ShapeFromFacts := by
  intro p q r s μ μ' hB hS hI
  obtain ⟨hA, hBb, hC, hD⟩ := hB
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ := hS
  obtain ⟨hI1, hI2⟩ := hI
  have iL1 : ∀ i, ((⌊leftWeightFirst p q r s μ i⌋ : ℤ) : ℚ) = leftWeightFirst p q r s μ i := fun i => hI1 (.inl i)
  have firstRealIndex : ∀ j, ((⌊leftWeightSecond p q r s μ j⌋ : ℤ) : ℚ) = leftWeightSecond p q r s μ j := fun j => hI1 (.inr j)
  have iL2 : ∀ k, ((⌊rightWeightFirst p q r s μ' k⌋ : ℤ) : ℚ) = rightWeightFirst p q r s μ' k := fun k => hI2 (.inl k)
  have secondRealIndex : ∀ l, ((⌊rightWeightSecond p q r s μ' l⌋ : ℤ) : ℚ) = rightWeightSecond p q r s μ' l := fun l => hI2 (.inr l)
  have eA : lpos (αA p q r s μ) = lpos (αP (rightWeightFirst p q r s μ')) := lpos_eq_of_sq hA
  have eB : lneg (αB p q r s μ) = lneg (αN (rightWeightSecond p q r s μ')) := lneg_eq_of_sq hBb
  have eC : lpos (αC p q r s μ) = lpos (αP (rightWeightSecond p q r s μ')) := lpos_eq_of_sq hC
  have eD : lneg (αD p q r s μ) = lneg (αN (rightWeightFirst p q r s μ')) := lneg_eq_of_sq hD
  have nA : nP (leftWeightFirst p q r s μ) = nP (rightWeightFirst p q r s μ') := hA.1
  have nB : nN (leftWeightFirst p q r s μ) = nN (rightWeightSecond p q r s μ') := hBb.1
  have nC : nP (leftWeightSecond p q r s μ) = nP (rightWeightSecond p q r s μ') := hC.1
  have nD : nN (leftWeightSecond p q r s μ) = nN (rightWeightFirst p q r s μ') := hD.1
  refine ⟨lpos (αA p q r s μ), lneg (αB p q r s μ), lpos (αC p q r s μ), lneg (αD p q r s μ),
    ?_, ?_, ?_, ?_, pairwise_lpos hA.2.1, pairwise_lneg hBb.2.1, pairwise_lpos hC.2.1, pairwise_lneg hD.2.1,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    simp only [lpos, List.mem_ofFn] at hv
    obtain ⟨i, rfl⟩ := hv
    exact_mod_cast pos_of_αP (leftWeightFirst p q r s μ) iL1 s1 i
  · intro v hv
    simp only [lpos, List.mem_ofFn] at hv
    obtain ⟨i, rfl⟩ := hv
    exact_mod_cast pos_of_αP (leftWeightSecond p q r s μ) firstRealIndex s3 i
  · intro v hv
    simp only [lneg, List.mem_reverse, List.mem_ofFn] at hv
    obtain ⟨i, rfl⟩ := hv
    have := pos_of_αN (leftWeightFirst p q r s μ) iL1 s2 i
    simp only [Left.neg_neg_iff, Nat.cast_pos]
    exact this
  · intro v hv
    simp only [lneg, List.mem_reverse, List.mem_ofFn] at hv
    obtain ⟨i, rfl⟩ := hv
    have := pos_of_αN (leftWeightSecond p q r s μ) firstRealIndex s4 i
    simp only [Left.neg_neg_iff, Nat.cast_pos]
    exact this
  · rw [length_lpos, length_lneg]; exact nP_add_nN_le _
  · rw [length_lpos, length_lneg]; exact nP_add_nN_le _
  · rw [length_lpos, length_lneg, nA, nD]; exact nP_add_nN_le _
  · rw [length_lpos, length_lneg, nC, nB]; exact nP_add_nN_le _
  · funext x
    rcases x with i | j
    · exact eq_pad (leftWeightFirst p q r s μ) iL1 s1 s2 i
    · exact eq_pad (leftWeightSecond p q r s μ) firstRealIndex s3 s4 j
  · rw [eA, eB, eC, eD]
    funext x
    rcases x with k | l
    · exact eq_pad (rightWeightFirst p q r s μ') iL2 s5 s6 k
    · exact eq_pad (rightWeightSecond p q r s μ') secondRealIndex s7 s8 l
end PI.FJM
