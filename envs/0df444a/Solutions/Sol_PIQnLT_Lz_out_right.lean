-- Prove2me | solution 1 for PIQnLT.Lz_out_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:11:15.490998+00:00
-- url     : https://prove2.me/submissions/751672e9-7f06-4957-b393-fcf7153c5d0f

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
theorem _root_.solution (X : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) (p q : Fin (2 * (i + r') + k + 1))
    (hq : ¬ (i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i)) : Lz k i r' X p q = 0 := by
  simp only [Lz]
  split_ifs <;> first | rfl | (exfalso; apply hq; assumption)
end PIQnLT
