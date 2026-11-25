-- Prove2me | solution 1 for PI.WFJM.eq_zero_of_hc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:05:51.109037+00:00
-- url     : https://prove2.me/submissions/d29cbcf2-e0df-49b0-9f9a-a24a4f1f50d6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr

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
theorem _root_.solution (x : MvPolynomial σ ℂ) (h : ∀ e, homogeneousComponent e x = 0) :
    x = 0 := by
  have hx : x = ∑ i ∈ Finset.range (x.totalDegree + 1), homogeneousComponent i x := by
    first
    | exact (sum_homogeneousComponent x).symm
    | exact sum_homogeneousComponent.symm
  rw [hx]
  exact Finset.sum_eq_zero fun i _ => h i
end PI.WFJM
