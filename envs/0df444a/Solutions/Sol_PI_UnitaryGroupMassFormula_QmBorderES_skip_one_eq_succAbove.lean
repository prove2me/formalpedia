-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmBorderES.skip_one_eq_succAbove
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:41:41.901028+00:00
-- url     : https://prove2.me/submissions/722a668b-7fa8-469a-b6ff-5159d13f01c3

import Definitions.Def_Formalism_PeriodIntegrals_QmBorderES
import Definitions.Def_Formalism_PeriodIntegrals_QmColExp
import Definitions.Def_Formalism_PeriodIntegrals_QmRowExp
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderSignIdentity_SkipOneEqSuccAbove

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
theorem _root_.solution {t : ℕ} (i : Fin (t + 1)) (j : Fin t) : PI.skip1 i j = i.succAbove j := by
  ext
  simp only [PI.skip1, Fin.succAbove, Fin.lt_def, Fin.coe_castSucc]
  split_ifs <;> simp_all
end PI.UnitaryGroupMassFormula.QmBorderES
