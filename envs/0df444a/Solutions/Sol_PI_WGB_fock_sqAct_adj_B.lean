-- Prove2me | solution 1 for PI.WGB.fock_sqAct_adj_B
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:29:33.658951+00:00
-- url     : https://prove2.me/submissions/1856ec69-af94-446c-84c8-648a27955191

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFacts
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ClosedEqNabla
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFEqSumOfSubsetB
import Theorems.Thm_PI_WGB_fockF_smul_left_B
import Theorems.Thm_PI_WGB_detPow_gStarB
import Theorems.Thm_Formalism_GradedWeylDivisibility_fockRowAdj


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
theorem _root_.solution {N : ℕ} (lam : DomWeight N) (g : GL (Fin N) ℂ) (x y : MvPolynomial (Fin N × Fin N) ℂ) :
    Formalism.REAL.fockF (sqAct ℂ N lam g x) y = Formalism.REAL.fockF x (sqAct ℂ N lam (gStarB g) y) := by
  unfold sqAct
  rw [fockF_smul_left_B, fockF_smul_right_B, detPow_gStarB, star_star, Formalism.GradedWeylDivisibility.fockRowAdj]
  congr 2
end PI.WGB
