-- Prove2me | solution 1 for PI.EF.log_two_le_log
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:19.985231+00:00
-- url     : https://prove2.me/submissions/c687c39a-58e6-4d95-94f0-e51d4ae8f35a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LogDerivBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex DirichletCharacter
namespace PI.EF
theorem _root_.solution {N : ℕ} [NeZero N] {x : ℝ} (hx : 2 ≤ x) : Real.log 2 ≤ Real.log (N * x) := by
  have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  exact Real.log_le_log (by norm_num) (by nlinarith)
end PI.EF
