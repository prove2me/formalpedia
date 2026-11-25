-- Prove2me | solution 1 for PI.DivPowInteg.Gen.vanR_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:43:56.638143+00:00
-- url     : https://prove2.me/submissions/6582e043-e8c3-4670-b2ad-d27a0b5ea8f7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_GenDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_GenVan
import Theorems.Thm_PI_DivPowInteg_Gen_mem_lowDeg
import Theorems.Thm_PI_DivPowInteg_Gen_pow_apply_eq_zero_of_lowDeg
import Theorems.Thm_PI_DivPowInteg_Gen_gdelta_mem_lowDeg_inr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.DivPowInteg PI.DivPowInteg.Gen
namespace PI.DivPowInteg.Gen
theorem _root_.solution : VanR := by
  intro K I J _ _ _ κ R n h
  exact pow_apply_eq_zero_of_lowDeg (gdelta κ) Sum.inr (fun t R hR => gdelta_mem_lowDeg_inr κ hR) n R
    (mem_lowDeg.mpr h)
end PI.DivPowInteg.Gen
