-- Prove2me | solution 1 for PI.EF.wsum_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:15.673733+00:00
-- url     : https://prove2.me/submissions/541d4014-97ea-4700-9696-3642af500205

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeight

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
open DirichletCharacter
namespace PI.EF
theorem _root_.solution {C : ℝ} (hC0 : 0 ≤ C) (hC : ZerosWindowWith C) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) {T t : ℝ} (_hT : 0 ≤ T) (ht : |t| ≤ T + 1) :
    wsum χ t ≤ C * Real.log (N * (T + 3)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  unfold wsum
  refine le_trans (hC N χ hχ t).2 ?_
  apply mul_le_mul_of_nonneg_left _ hC0
  apply Real.log_le_log (by positivity)
  apply mul_le_mul_of_nonneg_left _ hNpos.le
  linarith
end PI.EF
