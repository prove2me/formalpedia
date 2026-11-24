-- Prove2me | solution 1 for PI.FJMP.pderiv_eq_zero_of_noVar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:00.32492+00:00
-- url     : https://prove2.me/submissions/d8ed13f3-1d6d-41fc-9ea7-ab3f49a0c1d4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MemLeftHighestWeightOfIsMinimalJointVector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FJMP
open PI.FJM
variable {σ : Type*}
namespace PI.FJMP
theorem _root_.solution {P : MvPolynomial σ ℂ} {v : σ} (h : NoVar P v) : pderiv v P = 0 := by
  rw [P.as_sum, map_sum]
  refine Finset.sum_eq_zero fun e he => ?_
  rw [pderiv_monomial]
  simp [h e he]
end PI.FJMP
