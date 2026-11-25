-- Prove2me | solution 1 for PI.ScRefExists.Id.adOfLoc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:41:03.306807+00:00
-- url     : https://prove2.me/submissions/2b2f82cc-66c0-4267-b8a4-48258aafaaf2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_IdemLiftOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_IdemAd
import Theorems.Thm_PI_ScRefExists_Id_evA_apply
import Theorems.Thm_PI_ScRefExists_Id_eq_of_evA
import Theorems.Thm_PI_ScRefExists_Id_mkA_apply
import Theorems.Thm_PI_ScRefExists_Id_mkA_mem
import Theorems.Thm_PI_ScRefExists_Id_natCast_le_one
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open PI PI.ScRefExists PI.ScRefExists.Id
namespace PI.ScRefExists.Id
theorem _root_.solution : AdOfLoc := by
  unfold AdOfLoc LocIdem AdIdem
  intro hL F _ _ g α β hg hα hβ
  have hα' : ∀ v, Valued.v (α v) ≤ 1 := by
    intro v
    have h0 := (show ∀ v, α v ∈ HeightOneSpectrum.adicCompletionIntegers F v from hα) v
    exact memO.1 h0
  have hβ' : ∀ v, Valued.v (β v) ≤ 1 := by
    intro v
    have h0 := (show ∀ v, β v ∈ HeightOneSpectrum.adicCompletionIntegers F v from hβ) v
    exact memO.1 h0
  have key : ∀ v : HeightOneSpectrum (𝓞 F), ∃ c₁ c₂ : v.adicCompletion F,
      Valued.v c₁ ≤ 1 ∧ Valued.v c₂ ≤ 1 ∧
      (1 + (g : v.adicCompletion F) * α v) * (1 + (g : v.adicCompletion F) * c₁) ^ 2
          - 2 * (1 + (g : v.adicCompletion F) * c₁) * ((g : v.adicCompletion F) * c₂)
        = 1 + (g : v.adicCompletion F) * c₁ ∧
      ((g : v.adicCompletion F) * c₂) ^ 2
          - (g : v.adicCompletion F) * β v * (1 + (g : v.adicCompletion F) * c₁) ^ 2
        = -((g : v.adicCompletion F) * c₂) ∧
      ((g : v.adicCompletion F) * c₂) ^ 2
          - (1 + (g : v.adicCompletion F) * α v) * ((g : v.adicCompletion F) * c₂)
            * (1 + (g : v.adicCompletion F) * c₁)
          + (g : v.adicCompletion F) * β v * (1 + (g : v.adicCompletion F) * c₁) ^ 2 = 0 := by
    intro v
    by_cases hv : Valued.v ((g : ℕ) : v.adicCompletion F) < 1
    · exact hL F v g (α v) (β v) hg hv (hα' v) (hβ' v)
    · have h1 : Valued.v ((g : ℕ) : v.adicCompletion F) = 1 :=
        le_antisymm (natCast_le_one v g) (not_lt.mp hv)
      have hg0 : ((g : ℕ) : v.adicCompletion F) ≠ 0 := by
        intro h
        rw [h, map_zero] at h1
        exact zero_ne_one h1
      have hu : 1 + (g : v.adicCompletion F) * -((g : v.adicCompletion F))⁻¹ = 0 := by
        rw [mul_neg, mul_inv_cancel₀ hg0, add_neg_cancel]
      refine ⟨-((g : v.adicCompletion F))⁻¹, 0, ?_, ?_, ?_, ?_, ?_⟩
      · rw [Valuation.map_neg, map_inv₀, h1, inv_one]
      · rw [map_zero]
        exact zero_le'
      · rw [hu]
        simp
      · rw [hu]
        simp
      · rw [hu]
        simp
  choose c₁ c₂ h1 h2 e1 e2 e3 using key
  refine ⟨mkA c₁ h1, mkA c₂ h2, mkA_mem c₁ h1, mkA_mem c₂ h2, ?_, ?_, ?_⟩
  · apply eq_of_evA
    intro v
    simp only [map_add, map_mul, map_sub, map_pow, map_one, map_natCast, map_neg, map_ofNat,
      evA_apply, mkA_apply]
    exact e1 v
  · apply eq_of_evA
    intro v
    simp only [map_add, map_mul, map_sub, map_pow, map_one, map_natCast, map_neg, map_ofNat,
      evA_apply, mkA_apply]
    exact e2 v
  · apply eq_of_evA
    intro v
    simp only [map_add, map_mul, map_sub, map_pow, map_one, map_natCast, map_neg, map_ofNat,
      map_zero, evA_apply, mkA_apply]
    exact e3 v
end PI.ScRefExists.Id
