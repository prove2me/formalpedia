-- Prove2me | solution 1 for PI.DivPowInteg.Gen.powXR_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:01:05.733289+00:00
-- url     : https://prove2.me/submissions/bcc19bd9-3fa8-45d8-8e7b-c7ba448979c8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_GenDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_GenPow
import Theorems.Thm_PI_DivPowInteg_Gen_gdelta_dR_apply
import Theorems.Thm_PI_DivPowInteg_Gen_gdelta_pow_succ_apply
import Theorems.Thm_PI_DivPowInteg_Gen_gdelta_X_inr

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
theorem _root_.solution : PowXR := by
  unfold PowXR
  intro K I J _ _ _ κ j R n
  induction n with
  | zero => simp [gdelta_X_inr]
  | succ n ih =>
    rw [gdelta_pow_succ_apply κ (n + 1), ih, map_add, map_nsmul, gdelta_X_inr, gdelta_dR_apply,
      ← gdelta_pow_succ_apply, ← gdelta_pow_succ_apply, add_assoc, ← succ_nsmul']
end PI.DivPowInteg.Gen
