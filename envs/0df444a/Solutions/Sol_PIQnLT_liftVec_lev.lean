-- Prove2me | solution 1 for PIQnLT.liftVec_lev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:37:21.784397+00:00
-- url     : https://prove2.me/submissions/19fab0c0-9a1c-4d01-893a-fc7577b3f12d

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
theorem _root_.solution (v : Fin (2 * r' + k + 1) → ℂ) (j : Fin (2 * r' + k + 1)) :
    liftVec k i r' v (levPos k i r' j) = v j := by
  have hj := j.isLt
  have h1 : i ≤ (levPos k i r' j).val ∧ (levPos k i r' j).val < 2 * r' + k + 1 + i := by rw [lev_val]; omega
  simp only [liftVec]
  rw [dif_pos h1]
  congr 1
  apply Fin.ext
  show j.val + i - i = j.val
  omega
end PIQnLT
