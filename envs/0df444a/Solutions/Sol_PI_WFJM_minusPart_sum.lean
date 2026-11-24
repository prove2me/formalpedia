-- Prove2me | solution 1 for PI.WFJM.minusPart_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:34.048804+00:00
-- url     : https://prove2.me/submissions/a241fedf-c76f-494a-befd-316a4bd79c1d

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
theorem _root_.solution {ι : Type*} (t : Finset ι) (A : ι → Module.End ℂ (MvPolynomial σ ℂ))
    (P : MvPolynomial σ ℂ) : minusPart (∑ i ∈ t, A i) P = ∑ i ∈ t, minusPart (A i) P := by
  simp only [minusPart_eq_sum, LinearMap.sum_apply, map_sum]
  exact Finset.sum_comm
end PI.WFJM
