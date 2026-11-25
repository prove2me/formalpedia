-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.ModW.measurableSet_set
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:11:51.261808+00:00
-- url     : https://prove2.me/submissions/03ddc57b-4708-4f58-bd57-22c6015ea5bb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_ModBase

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
theorem _root_.solution (hG : IsMatGroup G) : MeasurableSet {x : MtM m | Matrix.of x ∈ G} :=
  (isClosed_set hG).measurableSet
end PI.QuotSetU.UnitaryGroupMassFormula.ModW
