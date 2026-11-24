-- Prove2me | solution 1 for P2M_PIQnLT__Lev_eq_d6fc93f29a45
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:15:45.306795+00:00
-- url     : https://prove2.me/submissions/a95a1927-0185-4ba4-afd0-3fa17151c54b

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementRP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_LzOutRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PIQnLT
open Formalism.REAL Formalism.QuantumDeterminants
variable {k i r' : ℕ}
namespace PIQnLT
theorem _root_.solution (X : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    ιLev k i r' X = Lz k i r' X + ιLev k i r' 0 := by
  ext p q
  simp only [ιLev, Lz, Matrix.add_apply]
  split_ifs <;> simp
end PIQnLT
