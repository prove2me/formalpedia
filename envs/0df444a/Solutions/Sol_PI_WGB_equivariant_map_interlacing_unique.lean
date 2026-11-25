-- Prove2me | solution 1 for PI.WGB.equivariant_map_interlacing_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:58:13.20261+00:00
-- url     : https://prove2.me/submissions/b3f5e3c1-2e97-49a9-8b89-54c0eda23d16

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFacts
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ConstructionD
import Theorems.Thm_PI_WGB_extremal_mem_D
import Theorems.Thm_PI_WGB_isEqv_zero_D
import Theorems.Thm_PI_WGB_isEqv_smul_D
import Theorems.Thm_PI_WGB_eq_on_of_extremal_D
import Theorems.Thm_PI_WGB_fixed_of_eqv_D

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
theorem _root_.solution (hI : PI.HwIrred) (he : ExtremalFacts) (ha : FixedLine) {n N : ℕ} (h : n + 1 = N)
    (lam : DomWeight N) (mu : DomWeight n)
    (φ φ' : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ)
    (hφ : IsEqv h mu lam φ) (hφ' : IsEqv h mu lam φ') (hne : ∃ s ∈ nablaSq ℂ n mu, φ' s ≠ 0) :
    Interlace h lam mu ∧ ∃ c : ℂ, ∀ s ∈ nablaSq ℂ n mu, φ s = c • φ' s := by
  have hmem := extremal_mem_D n mu
  have hne' : φ' (extremal ℂ n mu) ≠ 0 := by
    intro h0
    obtain ⟨s, hs, hs0⟩ := hne
    apply hs0
    have h3 := eq_on_of_extremal_D hI he h hφ' (isEqv_zero_D h mu lam) (by rw [h0, LinearMap.zero_apply]) s hs
    rw [h3, LinearMap.zero_apply]
  obtain ⟨⟨c, hc⟩, hint⟩ := ha n N h lam mu (φ (extremal ℂ n mu)) (φ' (extremal ℂ n mu)) (hφ.1 _ hmem)
    (hφ'.1 _ hmem) (fixed_of_eqv_D he h hφ) (fixed_of_eqv_D he h hφ') hne'
  refine ⟨hint, c, fun s hs => ?_⟩
  have h3 := eq_on_of_extremal_D hI he h hφ (isEqv_smul_D h hφ' c) (by rw [LinearMap.smul_apply, hc]) s hs
  rw [h3, LinearMap.smul_apply]
end PI.WGB
