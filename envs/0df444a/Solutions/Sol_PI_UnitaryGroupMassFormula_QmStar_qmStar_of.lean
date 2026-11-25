-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmStar.qmStar_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:11:01.155896+00:00
-- url     : https://prove2.me/submissions/7b379f3c-dce3-40cf-80c8-533396d1e04a

import Definitions.Def_Formalism_PeriodIntegrals_QmStar
import Definitions.Def_Formalism_PeriodIntegrals_QmRowForm
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerProductCast_OfFnProdIntCast
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmStar_star_qminor
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmStar_qminor_rev_rev

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmStar
namespace PI.UnitaryGroupMassFormula.QmStar
theorem _root_.solution (hrow : PI.RowForm) : PI.QmStar := by
  unfold PI.QmStar PI.StarMinor
  intro A _ _ _ _ n t E ε hE hs a b w
  rw [star_qminor E ε hs, ← hrow A n t E hE, qminor_rev_rev E hE]
end PI.UnitaryGroupMassFormula.QmStar
