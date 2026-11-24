-- Prove2me | solution 1 for PI.FockOneDegW.Core.key
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:14.386614+00:00
-- url     : https://prove2.me/submissions/f9f8e932-e7a1-4329-ba90-c55778c62887

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_EqZeroOfFockInnerSelfRe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_ExistsMonomialWeight
import Theorems.Thm_PI_FockOneDegW_Core_pd_comm
import Theorems.Thm_FockRaiseLowInner_fockInner_X_mul
import Theorems.Thm_FockRaiseLowInner_fockInner_mul_X


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
namespace PI.FockOneDegW.Core
theorem _root_.solution {σ : Type*} (v : MvPolynomial σ ℂ) (ac ad bc bd : σ) (hne : bc ≠ ad) :
    fockInner (pderiv ac (pderiv ad v)) (pderiv bc (pderiv bd v)) =
      fockInner (X bc * pderiv ac v) (X ad * pderiv bd v) := by
  rw [fockInner_mul_X, pderiv_mul, pderiv_X_of_ne hne, zero_mul, zero_add, fockInner_X_mul,
    pd_comm ad ac]
end PI.FockOneDegW.Core
