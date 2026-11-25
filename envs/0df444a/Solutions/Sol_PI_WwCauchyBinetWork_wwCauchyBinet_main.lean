-- Prove2me | solution 1 for PI.WwCauchyBinetWork.wwCauchyBinet_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:34:07.754708+00:00
-- url     : https://prove2.me/submissions/7c901ed7-bd47-4cd1-aef0-29573b2574e8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwCauchyBinet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_ExistsOePerm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CauchyBinet_WwCauchyBinetMain
import Theorems.Thm_PI_WwCauchyBinetWork_factor_expand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.WwCauchyBinetWork
open PI.WwCauchyBinet
namespace PI.WwCauchyBinetWork
theorem _root_.solution : WwCauchyBinet := by
  intro Lt _ _ k _ N nu y
  rw [finsum_eq_sum_of_fintype]
  simp only [DeX, factor_expand]
  simp only [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  simp only [minY, KM.nablaX, map_prod, Finset.prod_mul_distrib]
end PI.WwCauchyBinetWork
