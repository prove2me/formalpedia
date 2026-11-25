-- Prove2me | solution 1 for PIQnLT.Lz_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:17:02.286113+00:00
-- url     : https://prove2.me/submissions/3492d55f-8b22-48a3-b2ae-484d85fcff4f

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementRP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_LzOutRight
import Theorems.Thm_P2M_PIQnLT__Lev_eq_d6fc93f29a45

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
variable (hL : LevHom)
include hL
namespace PIQnLT
theorem _root_.solution : Lz k i r' 1 + ιLev k i r' 0 = 1 := by
  rw [← ιLev_eq]
  exact (hL k i r').1
end PIQnLT
