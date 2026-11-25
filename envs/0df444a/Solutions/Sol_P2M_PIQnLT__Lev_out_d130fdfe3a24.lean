-- Prove2me | solution 1 for P2M_PIQnLT__Lev_out_d130fdfe3a24
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:25:37.751698+00:00
-- url     : https://prove2.me/submissions/c9037cab-f2c7-409c-b921-7755aadddcfc

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
theorem _root_.solution (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) (p q : Fin (2 * (i + r') + k + 1))
    (hp : ¬ (i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i)) : ιLev k i r' g p q = if p = q then 1 else 0 := by
  simp only [ιLev]
  rw [dif_neg hp]
end PIQnLT
