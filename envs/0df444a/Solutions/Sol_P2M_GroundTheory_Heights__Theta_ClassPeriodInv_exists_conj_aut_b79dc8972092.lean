-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_ClassPeriodInv_exists_conj_aut_b79dc8972092
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:42:45.895649+00:00
-- url     : https://prove2.me/submissions/d94b3a35-7347-4fb8-80b8-0180ed0546b9

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
theorem _root_.solution (hK : finrank ℚ K = 2) (σ : K →+* ℂ) :
    ∃ g : K ≃ₐ[ℚ] K, ∀ x, σ (g x) = starRingEnd ℂ (σ x) := by
  have : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
  obtain ⟨g, hg⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ) σ
    ((starRingEnd ℂ).comp σ) (Subsingleton.elim _ _)
  exact ⟨g.symm, fun x => RingHom.congr_fun hg x⟩
end GroundTheory.Heights₂.Theta.ClassPeriodInv
