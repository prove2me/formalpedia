-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_ClassPeriodInv_negConj_mem_classReducedParams_01e2a9b546ba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:36:34.076875+00:00
-- url     : https://prove2.me/submissions/4295d26b-e73a-47ae-ad3c-5544acff0dad

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmEtaLogPeriodNegConjPf
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmClassPeriodInvConj
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_ClassPeriodInv_exists_inv_eq_conj_69225a47a7a0
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_ClassPeriodInv_isLatticeParam_conj_d29d060aaf70
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_ClassPeriodInv_negConj_mem_fd_478bf8519a1e

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
theorem _root_.solution (hK : finrank ℚ K = 2) (σ : K →+* ℂ)
    (hσ : ∃ x : K, (σ x).im ≠ 0) (A : ClassGroup (𝓞 K)) {τ : ℍ}
    (hτ : τ ∈ classReducedParams σ A) : negConj τ ∈ classReducedParams σ A⁻¹ := by
  obtain ⟨I, hIA, hfd, hpar⟩ := hτ
  obtain ⟨w, hw, hset⟩ := exists_inv_eq_conj hK σ hσ I
  refine ⟨I⁻¹, by rw [map_inv, hIA], negConj_mem_fd hfd, ?_⟩
  rw [hset]
  exact isLatticeParam_conj hpar hw
end GroundTheory.Heights₂.Theta.ClassPeriodInv
