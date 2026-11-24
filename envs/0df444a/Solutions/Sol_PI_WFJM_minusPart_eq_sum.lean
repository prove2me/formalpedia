-- Prove2me | solution 1 for PI.WFJM.minusPart_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:24:36.443599+00:00
-- url     : https://prove2.me/submissions/05e071d1-1c10-48c6-8f5f-8489bb36379d

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
theorem _root_.solution (A : Module.End ℂ (MvPolynomial σ ℂ)) (P : MvPolynomial σ ℂ) :
    minusPart A P = ∑ d ∈ Finset.range (P.totalDegree + 1),
      homogeneousComponent d (A (homogeneousComponent (d + 2) P)) := by
  unfold FockH1Action.minusPart
  apply finsum_eq_sum_of_support_subset
  intro d hd
  rw [Function.mem_support] at hd
  rw [Finset.mem_coe, Finset.mem_range]
  by_contra hlt
  apply hd
  show homogeneousComponent d (A (homogeneousComponent (d + 2) P)) = 0
  rw [homogeneousComponent_eq_zero (d + 2) P (by omega), map_zero, map_zero]
end PI.WFJM
