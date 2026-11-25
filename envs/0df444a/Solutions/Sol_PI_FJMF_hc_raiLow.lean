-- Prove2me | solution 1 for PI.FJMF.hc_raiLow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:04:50.415683+00:00
-- url     : https://prove2.me/submissions/0c81ab7f-98f5-440b-915b-b8baab9186eb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_ExistsMonomialWeight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_FockOperatorsKernel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_KroneckerOneRightSwap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MinDeg
import Theorems.Thm_PI_FJMF_hc_X
import Theorems.Thm_FockRL_hc_pderiv
import Theorems.Thm_PI_WFJM_hc_pderiv


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
theorem _root_.solution (l l' : Ln p q r s) (h : linePos l = linePos l') (e : ℕ) (Q : Pol p q r s) :
    homogeneousComponent e ((raiB l * lowB l') Q) = (raiB l * lowB l') (homogeneousComponent e Q) := by
  rw [Module.End.mul_apply, Module.End.mul_apply]
  cases hl : linePos l with
  | true =>
    have hl' : linePos l' = true := by rw [← h, hl]
    simp only [raiB, lowB, hl, hl', if_true, LinearMap.mulLeft_apply, Derivation.coeFn_coe]
    rw [hc_X]
    cases e with
    | zero => simp
    | succ k => simp [PI.WFJM.hc_pderiv]
  | false =>
    have hl' : linePos l' = false := by rw [← h, hl]
    simp only [raiB, lowB, hl, hl', Bool.false_eq_true, if_false, LinearMap.mulLeft_apply,
      Derivation.coeFn_coe, LinearMap.neg_apply]
    rw [map_neg, PI.WFJM.hc_pderiv, hc_X, if_pos (by omega)]
    simp
end PI.FJMF
