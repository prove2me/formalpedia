-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_ClassPeriodInv_negConj_mem_fd_478bf8519a1e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:42:58.026347+00:00
-- url     : https://prove2.me/submissions/18c18657-aed6-47f1-b1d3-e42177dc45e9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmEtaLogPeriodNegConjPf
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmClassPeriodInvConj

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open UpperHalfPlane ModularGroup ModularForm Complex NumberField Module
open scoped Real Modular MatrixGroups nonZeroDivisors
open GroundTheory.Heights₂.Theta.ClassPeriodInv
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Theta.ClassPeriodInv
theorem _root_.solution {τ : ℍ} (h : τ ∈ 𝒟) : negConj τ ∈ 𝒟 := by
  have hneg : ((negConj τ : ℍ) : ℂ) = -(starRingEnd ℂ (τ : ℂ)) := rfl
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · rw [hneg, Complex.normSq_neg, Complex.normSq_conj]
    exact h1
  · change |((negConj τ : ℍ) : ℂ).re| ≤ 1 / 2
    rw [hneg, Complex.neg_re, Complex.conj_re, abs_neg]
    exact h2
end GroundTheory.Heights₂.Theta.ClassPeriodInv
