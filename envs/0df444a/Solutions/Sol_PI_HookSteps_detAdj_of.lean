-- Prove2me | solution 1 for PI.HookSteps.detAdj_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:05:09.772961+00:00
-- url     : https://prove2.me/submissions/9edd20c5-429a-4211-bef2-1a91713325fa

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DetShiftNormOf
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQRowDivAdj
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockqLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DeterminantAdjugate
import Theorems.Thm_PI_HookSteps_fockQ_sum_left
import Theorems.Thm_PI_HookSteps_fockQ_sum_right
import Theorems.Thm_PI_HookSteps_fockQ_zsmul_left
import Theorems.Thm_PI_HookSteps_fockQ_zsmul_right
import Theorems.Thm_PI_HookSteps_fockQ_listX
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open PI PI.HookSteps
namespace PI.HookSteps
theorem _root_.solution (hX : MulXAdj) : DetAdj := by
  intro N f g
  classical
  rw [detX, Matrix.det_apply, Finset.sum_mul, fockQ_sum_left, detD, LinearMap.sum_apply,
    fockQ_sum_right]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, smul_mul_assoc, fockQ_zsmul_left, LinearMap.smul_apply, fockQ_zsmul_right]
  congr 1
  have h := fockQ_listX hX (List.ofFn fun j : Fin N => (σ j, j)) f g
  simp only [List.map_ofFn] at h
  rw [List.prod_ofFn] at h
  exact h
end PI.HookSteps
