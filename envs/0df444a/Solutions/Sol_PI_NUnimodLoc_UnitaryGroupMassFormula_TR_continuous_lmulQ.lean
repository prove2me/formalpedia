-- Prove2me | solution 1 for PI.NUnimodLoc.UnitaryGroupMassFormula.TR.continuous_lmulQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:18:26.938921+00:00
-- url     : https://prove2.me/submissions/047132da-2f88-435a-a186-9f1d605ccc3e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_Transf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology
noncomputable section
open PI PI.NUnimodLoc PI.NUnimodLoc.UnitaryGroupMassFormula PI.NUnimodLoc.UnitaryGroupMassFormula.TR
open PI Formalism.REAL
variable {m : ℕ}
namespace PI.NUnimodLoc.UnitaryGroupMassFormula.TR
theorem _root_.solution (a : Matrix (Fin m) (Fin m) ℂ) : Continuous (lmulQ (m := m) a) := by
  show Continuous fun x : Matrix (Fin m) (Fin m) ℂ => a * x
  exact continuous_const.matrix_mul continuous_id
end PI.NUnimodLoc.UnitaryGroupMassFormula.TR
