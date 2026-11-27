-- Prove2me | solution 1 for P2M_PIQnLT__Lev_in_out_b2d6b9d04e06
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:14:35.562802+00:00
-- url     : https://prove2.me/submissions/9ef1c911-27de-417b-973e-b93ebf3634de

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
    (hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i) (hq : ¬ (i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i)) :
    ιLev k i r' g p q = 0 := by
  simp only [ιLev]
  rw [dif_pos hp, dif_neg hq]
end PIQnLT
