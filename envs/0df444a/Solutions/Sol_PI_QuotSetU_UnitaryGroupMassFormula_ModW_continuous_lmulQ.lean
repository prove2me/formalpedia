-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.ModW.continuous_lmulQ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:27:14.065813+00:00
-- url     : https://prove2.me/submissions/c5011199-3910-45c2-82d5-1b4aa0342fdb

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
theorem _root_.solution (a : Matrix (Fin m) (Fin m) ℂ) : Continuous (lmulQ (m := m) a) := by
  unfold lmulQ
  exact continuous_const.matrix_mul continuous_id
end PI.QuotSetU.UnitaryGroupMassFormula.ModW
