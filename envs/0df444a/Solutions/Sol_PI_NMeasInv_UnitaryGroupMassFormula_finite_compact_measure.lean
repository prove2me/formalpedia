-- Prove2me | solution 1 for PI.NMeasInv.UnitaryGroupMassFormula.finite_compact_measure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:53:39.703258+00:00
-- url     : https://prove2.me/submissions/58f0c9ef-3bf4-4c9c-9257-f4b5c3e4a392

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
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_haarOn_props
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
theorem _root_.solution : FinCpt := by
  intro I r e f z _ μ hμ K hK
  exact (haarOn_props (PI.ScMuExists.UnitaryGroupMassFormula.NSub I e z)
    (PI.ScMuExists.UnitaryGroupMassFormula.isClosed_Ninf (I := I) (e := e) (z := z)) μ (haarOn_of I e z μ hμ)).1 K hK
end PI.NMeasInv.UnitaryGroupMassFormula
