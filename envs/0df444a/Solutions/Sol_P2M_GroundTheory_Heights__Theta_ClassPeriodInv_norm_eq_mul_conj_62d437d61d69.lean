-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_ClassPeriodInv_norm_eq_mul_conj_62d437d61d69
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:43:02.289408+00:00
-- url     : https://prove2.me/submissions/89ce6b83-699f-48a1-8195-488bbaed505d

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
open Classical
namespace GroundTheory.Heights₂.Theta.ClassPeriodInv
theorem _root_.solution (hK : finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    (g : K ≃ₐ[ℚ] K) (hg : ∀ x, σ (g x) = starRingEnd ℂ (σ x)) (x : K) :
    algebraMap ℚ K (Algebra.norm ℚ x) = x * g x := by
  have : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
  have hg1 : g ≠ 1 := by
    rintro rfl
    obtain ⟨y, hy⟩ := hσ
    have := hg y
    simp only [AlgEquiv.one_apply] at this
    exact hy (Complex.conj_eq_iff_im.mp this.symm)
  have hcard : Fintype.card Gal(K/ℚ) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, hK]
  have huniv : (Finset.univ : Finset Gal(K/ℚ)) = {1, g} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, hcard, Finset.card_pair (Ne.symm hg1)]
  rw [Algebra.norm_eq_prod_automorphisms, huniv, Finset.prod_pair (Ne.symm hg1)]
  rfl
end GroundTheory.Heights₂.Theta.ClassPeriodInv
