-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.ModW.isClosedEmbedding_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:29:55.699631+00:00
-- url     : https://prove2.me/submissions/8fa75b5a-ef91-4fc2-b2db-74d9305b5f1d

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
theorem _root_.solution : IsClosedEmbedding (val : MG G hG → MtM m) :=
  (isClosed_set hG).isClosedEmbedding_subtypeVal
end PI.QuotSetU.UnitaryGroupMassFormula.ModW
