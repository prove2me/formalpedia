-- Prove2me | solution 1 for PI.WGL.zComm_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:24:11.93206+00:00
-- url     : https://prove2.me/submissions/8fe1e2da-d3be-4721-af2c-523c031644d8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_NablaSqLeOfGen
import Theorems.Thm_PI_WGL_nablaSq_le_of_gen
import Theorems.Thm_PI_WGL_comp_gen
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivStable
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
namespace PI.WGL
theorem _root_.solution (h4 : PI.GTBranch) (hD : EqvDiv) (hW : EqvRowWt) : ZComm := by
  intro n N h lam Z hZ

  have hcomp : ∀ ν : Fin N → ℕ, ∀ f ∈ nablaSq ℂ N lam,
      Z (weightedHomogeneousComponent (rowW N N) ν f) = weightedHomogeneousComponent (rowW N N) ν (Z f) := by
    intro ν f hf
    have hle := nablaSq_le_of_gen h4 h lam
      (LinearMap.eqLocus (Z ∘ₗ weightedHomogeneousComponent (rowW N N) ν)
        (weightedHomogeneousComponent (rowW N N) ν ∘ₗ Z)) (by
        intro mu hmu φ hφ s hs
        obtain ⟨z, hz⟩ := hZ mu hmu φ hφ
        rw [LinearMap.mem_eqLocus]
        exact comp_gen hW h lam mu hmu φ hφ Z z hz ν s hs)
    have := hle hf
    rw [LinearMap.mem_eqLocus] at this
    exact this
  refine ⟨?_, ?_, ?_⟩
  · intro f hf
    have hle := nablaSq_le_of_gen h4 h lam ((nablaSq ℂ N lam).comap Z) (by
      intro mu hmu φ hφ s hs
      obtain ⟨z, hz⟩ := hZ mu hmu φ hφ
      rw [Submodule.mem_comap, hz s hs]
      exact Submodule.smul_mem _ z (hφ.1 s hs))
    exact hle hf
  · intro a b hab k f hf
    have hle := nablaSq_le_of_gen h4 h lam
      (LinearMap.eqLocus (Z ∘ₗ rowDivL ℂ (eRow h a) (eRow h b) k)
        (rowDivL ℂ (eRow h a) (eRow h b) k ∘ₗ Z)) (by
        intro mu hmu φ hφ s hs
        obtain ⟨z, hz⟩ := hZ mu hmu φ hφ
        rw [LinearMap.mem_eqLocus]
        simp only [LinearMap.comp_apply, rowDivL_apply]
        have hs' : rowDiv ℂ a b k s ∈ nablaSq ℂ n mu := rowDivStable ℂ n n mu.natW a b k s hs
        rw [← hD n N h mu lam φ hφ a b hab k s hs, hz _ hs', hz s hs, rowDiv_smul,
          hD n N h mu lam φ hφ a b hab k s hs])
    have := hle hf
    rw [LinearMap.mem_eqLocus] at this
    simpa only [LinearMap.comp_apply, rowDivL_apply] using this
  · intro ω f hf hhom
    rw [← hhom.weightedHomogeneousComponent_same, hcomp ω f hf]
    exact weightedHomogeneousComponent_isWeightedHomogeneous ω _
end PI.WGL
