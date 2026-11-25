-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.ModW.measEmb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:17:43.896662+00:00
-- url     : https://prove2.me/submissions/36fde7c2-16fe-4327-bd71-69ba64e2842d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_ModBase
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_ModW_measurableSet_set

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology
open scoped ENNReal NNReal
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.ModW
open PI
variable {m : ℕ}
variable {G : Set (Matrix (Fin m) (Fin m) ℂ)} {hG : IsMatGroup G}
open MG
namespace PI.QuotSetU.UnitaryGroupMassFormula.ModW
theorem _root_.solution : MeasurableEmbedding (val : MG G hG → MtM m) :=
  MeasurableEmbedding.subtype_coe (measurableSet_set hG)
end PI.QuotSetU.UnitaryGroupMassFormula.ModW
