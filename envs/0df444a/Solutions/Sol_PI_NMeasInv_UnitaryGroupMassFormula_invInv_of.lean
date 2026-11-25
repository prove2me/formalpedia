-- Prove2me | solution 1 for PI.NMeasInv.UnitaryGroupMassFormula.invInv_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:46:14.119565+00:00
-- url     : https://prove2.me/submissions/0dc08001-70d1-4a25-b792-e5016ad30486

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_NMeasInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_RightInvOfContract
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousUMatApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_HaarSub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ModOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstLeftInvMuInf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_Development
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_haarOn_of
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_invInv_of_right
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_isClosed_Ninf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory NumberField
open PI PI.NMeasInv PI.NMeasInv.UnitaryGroupMassFormula
namespace PI.NMeasInv.UnitaryGroupMassFormula
theorem _root_.solution (hR : RightInv) : InvInv := by
  intro I r e f z h μ hμ
  exact invInv_of_right (PI.ScMuExists.UnitaryGroupMassFormula.NSub I e z) (PI.ScMuExists.UnitaryGroupMassFormula.isClosed_Ninf (I := I) (e := e) (z := z))
    (haarOn_of I e z μ hμ) (hR I r e f z h μ hμ)
end PI.NMeasInv.UnitaryGroupMassFormula
