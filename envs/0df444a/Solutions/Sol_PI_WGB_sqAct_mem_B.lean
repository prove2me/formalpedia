-- Prove2me | solution 1 for PI.WGB.sqAct_mem_B
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:08:42.211466+00:00
-- url     : https://prove2.me/submissions/642c96f8-49b7-49ac-b4ee-2b4db1d8eb07

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFacts
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ClosedEqNabla
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFEqSumOfSubsetB
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
theorem _root_.solution {N : ℕ} (lam : DomWeight N) (g : GL (Fin N) ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ)
    (hf : f ∈ nablaSq ℂ N lam) : sqAct ℂ N lam g f ∈ nablaSq ℂ N lam := by
  unfold sqAct
  exact (nablaSq ℂ N lam).smul_mem _ (Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ N N lam.natW _ f hf)
end PI.WGB
