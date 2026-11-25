-- Prove2me | solution 1 for PI.NUnimodLoc.UnitaryGroupMassFormula.TR.continuous_rmulQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:57:55.778697+00:00
-- url     : https://prove2.me/submissions/7931eb14-e6cd-44b1-b670-9bc3d96b2005

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
theorem _root_.solution (a : Matrix (Fin m) (Fin m) ℂ) : Continuous (rmulQ (m := m) a) := by
  show Continuous fun x : Matrix (Fin m) (Fin m) ℂ => x * a
  exact continuous_id.matrix_mul continuous_const
end PI.NUnimodLoc.UnitaryGroupMassFormula.TR
