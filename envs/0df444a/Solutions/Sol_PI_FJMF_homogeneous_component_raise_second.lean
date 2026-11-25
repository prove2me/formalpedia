-- Prove2me | solution 1 for PI.FJMF.homogeneous_component_raise_second
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:11:50.934747+00:00
-- url     : https://prove2.me/submissions/d418259b-cc30-496f-bf5a-a821d4a4ba83

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_ExistsMonomialWeight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_FockOperatorsKernel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_KroneckerOneRightSwap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MinDeg
import Theorems.Thm_PI_FJMF_hc_raiLow
import Theorems.Thm_PI_FJMF_sameBlock_linePos_second

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
open PI PI.FJMF
variable {p q r s : ℕ}
namespace PI.FJMF
theorem _root_.solution {c d : Ix r s} (hcd : sameBlock c d) (e : ℕ) (Q : Pol p q r s) :
    homogeneousComponent e (PI.FJM.rai2 (p := p) (q := q) c d Q) =
      PI.FJM.rai2 (p := p) (q := q) c d (homogeneousComponent e Q) := by
  simp only [PI.FJM.rai2, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun a _ => hc_raiLow _ _ (sameBlock_linePos_second hcd a) e Q
end PI.FJMF
