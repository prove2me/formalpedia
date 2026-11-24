-- Prove2me | solution 1 for PIQnLT.Lz_lev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:37:26.122338+00:00
-- url     : https://prove2.me/submissions/73158d60-eedd-4342-937a-22e29cdd8741

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementRP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_LzOutRight
import Theorems.Thm_PIQnLT_lev_val

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
theorem _root_.solution (X : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) (p q : Fin (2 * r' + k + 1)) :
    Lz k i r' X (levPos k i r' p) (levPos k i r' q) = X p q := by
  have hp := p.isLt
  have hq := q.isLt
  have h1 : i ≤ (levPos k i r' p).val ∧ (levPos k i r' p).val < 2 * r' + k + 1 + i := by rw [lev_val]; omega
  have h2 : i ≤ (levPos k i r' q).val ∧ (levPos k i r' q).val < 2 * r' + k + 1 + i := by rw [lev_val]; omega
  simp only [Lz]
  rw [dif_pos h1, dif_pos h2]
  congr 1 <;> apply Fin.ext
  · show p.val + i - i = p.val
    omega
  · show q.val + i - i = q.val
    omega
end PIQnLT
