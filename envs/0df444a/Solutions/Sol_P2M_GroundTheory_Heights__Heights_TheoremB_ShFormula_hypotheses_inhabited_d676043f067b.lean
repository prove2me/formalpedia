-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TheoremB_ShFormula_hypotheses_inhabited_d676043f067b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:04:16.183354+00:00
-- url     : https://prove2.me/submissions/de8f090a-e288-474d-9d27-cd2754b4d653

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TheoremB_blockPowerSum_isHomogeneous_4d2f50dbc507

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.TheoremB
open MvPolynomial Finset
variable (d : IndexData)
namespace GroundTheory.Heights₂.Heights.TheoremB
namespace ShFormula
theorem _root_.solution :
    sampleF ≠ 0 ∧ sampleF.IsHomogeneous (d1.D + 1) ∧
      (∀ k ∈ Icc 1 d1.N, ∀ τ' : Fin d1.f, (sampleQ k τ').IsHomogeneous (d1.D + 1 - k)) ∧
      RestTerms.IsPowerSumDecomposition d1.f d1.N sampleF sampleQ := by
  refine ⟨?_, ?_, ?_, rfl⟩
  · intro h
    have h1 := congrArg (eval (fun _ => (1 : ℚ))) h
    have hI : Icc 1 d1.N = {1, 2} := by decide
    simp [sampleF, sampleQ, hI, RestTerms.blockPowerSum] at h1
  · apply IsHomogeneous.sum
    intro k _
    apply IsHomogeneous.sum
    intro τ _
    by_cases hk : k = 1
    · subst hk
      simp only [sampleQ, if_true]
      exact (blockPowerSum_isHomogeneous _ _ 1 τ).mul (isHomogeneous_X ℚ _)
    · simp only [sampleQ, if_neg hk, mul_zero]
      exact isHomogeneous_zero _ _ _
  · intro k _ τ
    by_cases hk : k = 1
    · subst hk
      simp only [sampleQ, if_true]
      exact isHomogeneous_X ℚ _
    · simp only [sampleQ, if_neg hk]
      exact isHomogeneous_zero _ _ _
end ShFormula
end GroundTheory.Heights₂.Heights.TheoremB
