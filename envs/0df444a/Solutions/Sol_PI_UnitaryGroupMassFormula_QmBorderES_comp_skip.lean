-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmBorderES.comp_skip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:58:01.385741+00:00
-- url     : https://prove2.me/submissions/334f296b-9512-432f-8493-e8499db1c4a7

import Definitions.Def_Formalism_PeriodIntegrals_QmBorderES
import Definitions.Def_Formalism_PeriodIntegrals_QmColExp
import Definitions.Def_Formalism_PeriodIntegrals_QmRowExp
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderSignIdentity_SkipOneEqSuccAbove
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderES_skip_one_eq_succAbove

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmBorderES
namespace PI.UnitaryGroupMassFormula.QmBorderES
theorem _root_.solution {n t : ℕ} (v : Fin (t + 1) → Fin n) (w : Fin (t + 1)) :
    (v ∘ PI.skip1 w : Fin t → Fin n) = v ∘ w.succAbove := by
  funext j
  exact congrArg v (skip_one_eq_succAbove w j)
end PI.UnitaryGroupMassFormula.QmBorderES
