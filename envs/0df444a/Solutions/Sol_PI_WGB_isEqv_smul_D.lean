-- Prove2me | solution 1 for PI.WGB.isEqv_smul_D
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:27:20.011478+00:00
-- url     : https://prove2.me/submissions/86bab49d-9b3a-4edc-b755-d6f2930ffd56

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFacts
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ConstructionD
import Theorems.Thm_PI_WGB_sqLinD_apply

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
theorem _root_.solution {n N : ℕ} (h : n + 1 = N) {mu : DomWeight n} {lam : DomWeight N}
    {φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ} (hφ : IsEqv h mu lam φ) (c : ℂ) :
    IsEqv h mu lam (c • φ) := by
  refine ⟨fun s hs => ?_, fun g s hs => ?_⟩
  · rw [LinearMap.smul_apply]
    exact Submodule.smul_mem _ c (hφ.1 s hs)
  · rw [LinearMap.smul_apply, LinearMap.smul_apply, hφ.2 g s hs, ← sqLinD_apply, ← sqLinD_apply, map_smul]
end PI.WGB
