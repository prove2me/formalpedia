-- Prove2me | solution 1 for PI.FJMF.homogeneous_component_raise_first
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:11:43.456799+00:00
-- url     : https://prove2.me/submissions/c3df2473-ae2e-4d66-9e11-264df2c0e4b6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_ExistsMonomialWeight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_FockOperatorsKernel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_KroneckerOneRightSwap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MinDeg
import Theorems.Thm_PI_FJMF_hc_raiLow
import Theorems.Thm_PI_FJMF_sameBlock_linePos_first

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
theorem _root_.solution {a b : Ix p q} (hab : sameBlock a b) (e : ℕ) (Q : Pol p q r s) :
    homogeneousComponent e (PI.FJM.rai1 (r := r) (s := s) a b Q) =
      PI.FJM.rai1 (r := r) (s := s) a b (homogeneousComponent e Q) := by
  simp only [PI.FJM.rai1, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun c _ => hc_raiLow _ _ (sameBlock_linePos_first hab c) e Q
end PI.FJMF
