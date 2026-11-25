-- Prove2me | solution 1 for PI.DivPowInteg.Gen.powXL_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:59:44.257877+00:00
-- url     : https://prove2.me/submissions/bf145fd9-7cfe-49cf-a567-2862ea2032b7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_GenDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_GenPow
import Theorems.Thm_PI_DivPowInteg_Gen_gdelta_dL_apply
import Theorems.Thm_PI_DivPowInteg_Gen_gdelta_pow_succ_apply
import Theorems.Thm_PI_DivPowInteg_Gen_gdelta_X_inl

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
theorem _root_.solution : PowXL := by
  unfold PowXL
  intro K I J _ _ _ κ i R n
  induction n with
  | zero => simp [gdelta_X_inl]
  | succ n ih =>
    rw [gdelta_pow_succ_apply κ (n + 1), ih, map_add, map_nsmul, gdelta_X_inl, gdelta_dL_apply,
      ← gdelta_pow_succ_apply, ← gdelta_pow_succ_apply, add_assoc, ← succ_nsmul']
end PI.DivPowInteg.Gen
