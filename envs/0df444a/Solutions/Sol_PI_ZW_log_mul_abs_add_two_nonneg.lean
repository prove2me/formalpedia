-- Prove2me | solution 1 for PI.ZW.log_mul_abs_add_two_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:15:56.851254+00:00
-- url     : https://prove2.me/submissions/69d0df57-4173-49d5-9a7e-dbc4c6b3bb80

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightHalfWith
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_FinsumMemLeFinsumMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.ZW
open DirichletCharacter
namespace PI.ZW
theorem _root_.solution (N : ℕ) [NeZero N] (t : ℝ) : 0 ≤ Real.log (N * (|t| + 2)) := by
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  apply Real.log_nonneg
  nlinarith [abs_nonneg t]
end PI.ZW
