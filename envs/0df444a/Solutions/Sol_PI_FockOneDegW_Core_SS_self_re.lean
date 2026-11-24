-- Prove2me | solution 1 for PI.FockOneDegW.Core.SS_self_re
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:26.27274+00:00
-- url     : https://prove2.me/submissions/7155d7ca-8b71-405d-9c85-7c38531339fe

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_EqZeroOfFockInnerSelfRe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_ExistsMonomialWeight

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
open PI PI.FockOneDegW PI.FockOneDegW.Core
open PI.FockOneDegW PI.FockOneDegW.Inner PI.FockOneDegW.Diag
variable {p q r s : ℕ}
namespace PI.FockOneDegW.Core
theorem _root_.solution (v : Pol p q r s) (a : Ix p q) :
    (SS v a a).re = ∑ c : Ix r s, ∑ d : Ix r s, (fockInner (gg v a c d) (gg v a c d)).re := by
  unfold SS
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Complex.re_sum]
end PI.FockOneDegW.Core
