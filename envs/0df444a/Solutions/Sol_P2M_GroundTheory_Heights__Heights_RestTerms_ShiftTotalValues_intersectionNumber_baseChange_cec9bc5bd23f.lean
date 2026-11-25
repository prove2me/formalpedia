-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_ShiftTotalValues_intersectionNumber_baseChange_cec9bc5bd23f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:53:56.653654+00:00
-- url     : https://prove2.me/submissions/953ab2bf-fae3-4ed2-99b1-3ed5355564bd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_flagIntegral_C_mul_710bd134373c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_sumPderiv_restPolynomial_323c14e620df

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
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace ShiftTotalValues
theorem _root_.solution : ShiftTotalValues.Statement := by
  classical
  intro f r a τ
  have hsum : ∑ σ : Fin f, (if σ = τ then (1 : ℚ) else 0) = 1 := by simp
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [shiftFunctional, Flag.sumPderiv_restPolynomial f r a .last τ _ (fun _ => 0)
      (fun σ => if σ = τ then 1 else 0) (fun σ i => ?_) (fun σ i => ?_), Flag.flagIntegral_C_mul]
    · simp
    · rw [if_neg (by rintro ⟨-, hh⟩; have hh2 := (Finset.mem_filter.mp hh).2; simp [yIndex, SmallBlock.jIndex] at hh2)]; simp
    · by_cases h : σ = τ <;> simp [zIndex, SmallBlock.jIndex, Finset.mem_filter, h] <;> (try exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [SmallBlock.jIndex]⟩) <;> (try (rw [if_neg]; intro hh; have hh2 := (Finset.mem_filter.mp hh.2).2; simp [SmallBlock.jIndex] at hh2))
  · rw [totalFunctional, Flag.sumPderiv_restPolynomial f r a .last τ _
      (fun σ => if σ = τ then 1 else 0) (fun σ => if σ = τ then 1 else 0) (fun σ i => ?_)
      (fun σ i => ?_), Flag.flagIntegral_C_mul, hsum, fibreDegree]
    · simp [SmallBlock.sign]
    · by_cases h : σ = τ <;> simp [yIndex, h]
    · by_cases h : σ = τ <;> simp [zIndex, h]
  · rw [shiftFunctional, Flag.sumPderiv_restPolynomial f r a .first τ _
      (fun σ => if σ = τ then 1 else 0) (fun _ => 0) (fun σ i => ?_) (fun σ i => ?_),
      Flag.flagIntegral_C_mul, hsum, fibreDegree]
    · simp [SmallBlock.sign]
    · by_cases h : σ = τ <;> simp [yIndex, SmallBlock.jIndex, Finset.mem_filter, h] <;> (try exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [SmallBlock.jIndex]⟩) <;> (try (rw [if_neg]; intro hh; have hh2 := (Finset.mem_filter.mp hh.2).2; simp [SmallBlock.jIndex] at hh2))
    · rw [if_neg (by rintro ⟨-, hh⟩; have hh2 := (Finset.mem_filter.mp hh).2; simp [zIndex, SmallBlock.jIndex] at hh2)]; simp
  · rw [totalFunctional, Flag.sumPderiv_restPolynomial f r a .first τ _
      (fun σ => if σ = τ then 1 else 0) (fun σ => if σ = τ then 1 else 0) (fun σ i => ?_)
      (fun σ i => ?_), Flag.flagIntegral_C_mul, hsum, fibreDegree]
    · simp [SmallBlock.sign]
    · by_cases h : σ = τ <;> simp [yIndex, h]
    · by_cases h : σ = τ <;> simp [zIndex, h]
end ShiftTotalValues
end GroundTheory.Heights₂.Heights.RestTerms
