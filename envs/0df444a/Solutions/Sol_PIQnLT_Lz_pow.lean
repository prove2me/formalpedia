-- Prove2me | solution 1 for PIQnLT.Lz_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:32:47.756591+00:00
-- url     : https://prove2.me/submissions/48fa4f71-d705-41eb-b040-b5279981da47

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementRP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_LzOutRight
import Theorems.Thm_PIQnLT_Lz_mul

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
theorem _root_.solution (X : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) (n : ℕ) :
    Lz k i r' (X ^ (n + 1)) = Lz k i r' X ^ (n + 1) := by
  induction n with
  | zero => rw [zero_add, pow_one, pow_one]
  | succ n ih => rw [pow_succ, Lz_mul hL, ih, ← pow_succ]
end PIQnLT
