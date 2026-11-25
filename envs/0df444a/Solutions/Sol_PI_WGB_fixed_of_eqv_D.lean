-- Prove2me | solution 1 for PI.WGB.fixed_of_eqv_D
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:33:09.193514+00:00
-- url     : https://prove2.me/submissions/0f98418f-c049-4834-a671-82a82eb9f59e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFacts
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ConstructionD
import Theorems.Thm_PI_WGB_extremal_mem_D

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
theorem _root_.solution (he : ExtremalFacts) {n N : ℕ} (h : n + 1 = N) {mu : DomWeight n} {lam : DomWeight N}
    {φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ} (hφ : IsEqv h mu lam φ) :
    IsFixedW h lam mu (φ (extremal ℂ n mu)) := by
  have hmem := extremal_mem_D n mu
  refine ⟨fun g hg1 hg2 => ?_, fun t => ?_⟩
  · rw [← hφ.2 g _ hmem, (he n mu).1 g hg1 hg2]
  · rw [← hφ.2 _ _ hmem, (he n mu).2.1 t, map_smul]
end PI.WGB
