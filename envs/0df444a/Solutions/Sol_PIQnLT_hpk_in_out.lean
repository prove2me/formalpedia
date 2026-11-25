-- Prove2me | solution 1 for PIQnLT.hpk_in_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:32:43.598414+00:00
-- url     : https://prove2.me/submissions/4961041c-084e-4986-844d-ff6d97b6dea9

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
theorem _root_.solution (p q : Fin (2 * (i + r') + k + 1))
    (hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i) (hq : ¬ (i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i)) :
    Hpk k (i + r') p q = 0 := by
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)
end PIQnLT
