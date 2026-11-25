-- Prove2me | solution 1 for PI.HookSteps.fockQ_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:57:30.939405+00:00
-- url     : https://prove2.me/submissions/5428b9f8-b3f9-487e-a144-047c6932b3e7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DetShiftNormOf
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQRowDivAdj
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockqLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DeterminantAdjugate
import Theorems.Thm_PI_HookSteps_fockQ_zero_left
import Theorems.Thm_Formalism_GradedWeylDivisibility_lfockq_add_left
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
theorem _root_.solution {σ ι : Type*} (s : Finset ι) (F : ι → MvPolynomial σ ℚ) (g : MvPolynomial σ ℚ) :
    fockQ (∑ i ∈ s, F i) g = ∑ i ∈ s, fockQ (F i) g := by
  classical
  exact Finset.induction_on s (by simp [fockQ_zero_left]) fun a s ha ih => by
    rw [Finset.sum_insert ha, Finset.sum_insert ha, lfockq_add_left, ih]
end PI.HookSteps
