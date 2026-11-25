-- Prove2me | solution 1 for PI.FockOneDegW.fock_operators_kernel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:47:14.301718+00:00
-- url     : https://prove2.me/submissions/0abba43c-87bc-44f0-a461-178f59d13160

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_KroneckerMapOneRightNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_BlockDiagonalPreservesDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_RaisingLoweringSplit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_FockOperatorsKernel
import Theorems.Thm_PI_FockOneDegW_omE_same
import Theorems.Thm_PI_FockOneDegW_fockAct1_Eab_apply
import Theorems.Thm_PI_FockOneDegW_posOp_apply
import Theorems.Thm_PI_FockOneDegW_negOp_apply
import Theorems.Thm_PI_FockOneDegW_sum_half

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
open PI PI.FockOneDegW
namespace PI.FockOneDegW
theorem _root_.solution : OpsK := by
  intro p q r s a b hab
  apply LinearMap.ext
  intro P
  rw [fockAct1_Eab_apply]
  simp only [LinearMap.add_apply, LinearMap.sub_apply, posOp_apply, negOp_apply]
  rw [Finset.sum_congr rfl fun c _ => omE_same a b c hab P, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  congr 1
  split_ifs with h
  · subst h
    simp only [↓reduceIte, LinearMap.smul_apply, Module.End.one_apply]
    rw [← Finset.sum_smul, sum_half]
  · simp
end PI.FockOneDegW
