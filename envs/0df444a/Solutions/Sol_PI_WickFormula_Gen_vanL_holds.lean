-- Prove2me | solution 1 for PI.WickFormula.Gen.vanL_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:37:51.90401+00:00
-- url     : https://prove2.me/submissions/a4a3ee16-f1c0-44e9-b414-ab4110e511e4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_GenDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_GenVan
import Theorems.Thm_PI_WickFormula_Gen_mem_lowDeg
import Theorems.Thm_PI_WickFormula_Gen_pow_apply_eq_zero_of_lowDeg
import Theorems.Thm_PI_WickFormula_Gen_gdelta_mem_lowDeg_inl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.WickFormula PI.WickFormula.Gen
namespace PI.WickFormula.Gen
theorem _root_.solution : VanL := by
  unfold VanL
  intro K I J _ _ _ κ R n h
  exact pow_apply_eq_zero_of_lowDeg _ _ (fun t R h => gdelta_mem_lowDeg_inl κ h) n R (mem_lowDeg.mpr h)
end PI.WickFormula.Gen
