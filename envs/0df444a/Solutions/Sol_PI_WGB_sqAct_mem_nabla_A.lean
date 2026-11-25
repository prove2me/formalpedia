-- Prove2me | solution 1 for PI.WGB.sqAct_mem_nabla_A
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:11:32.493501+00:00
-- url     : https://prove2.me/submissions/3e38785d-5e2c-4d59-b691-6f566b6cde94

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFacts
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFactsProofA
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylRowStable


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
theorem _root_.solution (n : ℕ) (mu : DomWeight n) (g : GL (Fin n) ℂ)
    (s : MvPolynomial (Fin n × Fin n) ℂ) (hs : s ∈ nablaSq ℂ n mu) :
    sqAct ℂ n mu g s ∈ nablaSq ℂ n mu := by
  unfold sqAct
  exact Submodule.smul_mem _ _ (Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ n n mu.natW _ s hs)
end PI.WGB
