-- Prove2me | solution 1 for PI.WFJM.minusPart_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:01.184831+00:00
-- url     : https://prove2.me/submissions/f34eaf6f-b99b-44ec-9be9-92f9d7008371

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Theorems.Thm_PI_WFJM_minusPart_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.WFJM
open MvPolynomial
open PI.FJM
open MvPolynomial
variable {σ : Type*}
namespace PI.WFJM
theorem _root_.solution (c : ℂ) (A : Module.End ℂ (MvPolynomial σ ℂ)) (P : MvPolynomial σ ℂ) :
    minusPart (c • A) P = c • minusPart A P := by
  simp only [minusPart_eq_sum, LinearMap.smul_apply, map_smul, Finset.smul_sum]
end PI.WFJM
