-- Prove2me | solution 1 for PI.WGB.detPow_gStarB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:05:57.448782+00:00
-- url     : https://prove2.me/submissions/946bad84-5376-4309-8998-ee5e87bbe68a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFacts
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ClosedEqNabla
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFEqSumOfSubsetB
import Theorems.Thm_PI_WGB_gStarB_val

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
theorem _root_.solution {N : ℕ} (g : GL (Fin N) ℂ) (k : ℤ) :
    detPow ℂ N (gStarB g) k = star (detPow ℂ N g k) := by
  unfold detPow
  rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.GeneralLinearGroup.val_det_apply, gStarB_val, Matrix.det_conjTranspose, star_zpow₀]
end PI.WGB
