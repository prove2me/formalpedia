-- Prove2me | solution 1 for PI.WGB.eq_on_of_extremal_D
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:33:06.484986+00:00
-- url     : https://prove2.me/submissions/e1bcaaf3-94ed-4620-9ba8-1f144abba2ae

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFacts
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ConstructionD
import Theorems.Thm_PI_WGB_extremal_mem_D
import Theorems.Thm_PI_WGB_extremal_ne_D

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions MvPolynomial
namespace PI.WGB
theorem _root_.solution (hI : PI.HwIrred) (he : ExtremalFacts) {n N : ℕ} (h : n + 1 = N)
    {mu : DomWeight n} {lam : DomWeight N}
    {φ ψ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ}
    (hφ : IsEqv h mu lam φ) (hψ : IsEqv h mu lam ψ)
    (hext : φ (extremal ℂ n mu) = ψ (extremal ℂ n mu)) : ∀ s ∈ nablaSq ℂ n mu, φ s = ψ s := by
  let U : Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ) := nablaSq ℂ n mu ⊓ LinearMap.ker (φ - ψ)
  have hU : U ≤ nablaSq ℂ n mu := inf_le_left
  have hstab : ∀ (g : GL (Fin n) ℂ), ∀ f ∈ U, sqAct ℂ n mu g f ∈ U := by
    rintro g f ⟨hf1, hf2⟩
    refine ⟨(he n mu).2.2 g f hf1, ?_⟩
    have hf2' : φ f = ψ f := by
      rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hf2
      exact hf2
    show sqAct ℂ n mu g f ∈ LinearMap.ker (φ - ψ)
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, hφ.2 g f hf1, hψ.2 g f hf1, hf2']
  rcases (hI n mu).2.1 U hU hstab with hbot | htop
  · exfalso
    have he_mem : extremal ℂ n mu ∈ U :=
      ⟨extremal_mem_D n mu, by
        show extremal ℂ n mu ∈ LinearMap.ker (φ - ψ)
        rw [LinearMap.mem_ker, LinearMap.sub_apply, hext, sub_self]⟩
    rw [hbot] at he_mem
    exact extremal_ne_D n mu ((Submodule.mem_bot ℂ).mp he_mem)
  · intro s hs
    have hsU : s ∈ U := by rw [htop]; exact hs
    have h2 : s ∈ LinearMap.ker (φ - ψ) := hsU.2
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h2
    exact h2
end PI.WGB
