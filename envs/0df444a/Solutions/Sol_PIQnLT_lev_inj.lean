-- Prove2me | solution 1 for PIQnLT.lev_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:37:27.747022+00:00
-- url     : https://prove2.me/submissions/f54854d2-5916-4957-95f4-1198a73d3ca3

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
theorem _root_.solution : Function.Injective (levPos k i r') := by
  intro a b h
  apply Fin.ext
  have h' := congrArg Fin.val h
  rw [lev_val, lev_val] at h'
  omega
end PIQnLT
