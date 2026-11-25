-- Prove2me | solution 1 for PI.WickFormula.Gen.powXL_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:14:10.578819+00:00
-- url     : https://prove2.me/submissions/f9b32576-f5b2-41c7-917b-983957ea6241

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_GenDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_GenPow
import Theorems.Thm_PI_WickFormula_Gen_gdelta_dL_apply
import Theorems.Thm_PI_WickFormula_Gen_gdelta_pow_succ_apply
import Theorems.Thm_PI_WickFormula_Gen_gdelta_X_inl

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
theorem _root_.solution : PowXL := by
  intro K I J _ _ _ κ i R n
  induction n with
  | zero => simp [gdelta_X_inl]
  | succ n ih =>
    rw [gdelta_pow_succ_apply, ih, map_add, gdelta_X_inl, map_nsmul,
      ← gdelta_pow_succ_apply, gdelta_dL_apply,
      ← gdelta_pow_succ_apply, succ_nsmul _ (n + 1)]
    abel
end PI.WickFormula.Gen
