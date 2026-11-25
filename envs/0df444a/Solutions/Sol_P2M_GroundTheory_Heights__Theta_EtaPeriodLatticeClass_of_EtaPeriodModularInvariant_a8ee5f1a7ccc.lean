-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_EtaPeriodLatticeClass_of_EtaPeriodModularInvariant_a8ee5f1a7ccc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:51:40.699686+00:00
-- url     : https://prove2.me/submissions/4015b526-59ae-431a-90f8-fdbcd36647a2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmEtaPeriodLatticeClassPf
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_EtaPeriodLatticeClass_exists_SL_smul_eq_df0b2626b635

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
open UpperHalfPlane ModularGroup ModularForm Complex
open scoped Real Modular MatrixGroups
open GroundTheory.Heights₂.Theta.EtaPeriodLatticeClass
namespace GroundTheory.Heights₂.Theta.EtaPeriodLatticeClass
theorem _root_.solution (hinv : EtaPeriodModularInvariant.Statement) :
    EtaPeriodLatticeClass.Statement := by
  rintro Λ τ τ' ⟨c, hc, hΛ⟩ ⟨c', hc', hΛ'⟩
  have h1 : ∀ z ∈ latticeOf (τ : ℂ), c' / c * z ∈ latticeOf (τ' : ℂ) := by
    intro z hz
    rw [← hΛ] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    rw [← hΛ']
    exact ⟨x, hx, by field_simp⟩
  have h2 : ∀ w ∈ latticeOf (τ' : ℂ), (c' / c)⁻¹ * w ∈ latticeOf (τ : ℂ) := by
    intro w hw
    rw [← hΛ'] at hw
    obtain ⟨x, hx, rfl⟩ := hw
    rw [← hΛ]
    exact ⟨x, hx, by field_simp⟩
  obtain ⟨γ, hγ⟩ := exists_SL_smul_eq (div_ne_zero hc' hc) h1 h2
  rw [← hγ, hinv]
end GroundTheory.Heights₂.Theta.EtaPeriodLatticeClass
