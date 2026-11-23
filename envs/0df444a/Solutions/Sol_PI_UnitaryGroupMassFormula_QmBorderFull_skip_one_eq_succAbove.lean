-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmBorderFull.skip_one_eq_succAbove
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:11.041275+00:00
-- url     : https://prove2.me/submissions/4abf0270-2b87-4015-a6e2-8af121c7a567

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_SkipOneEqSuccAbove
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_val_succAbove

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmBorderFull
open PI
namespace PI.UnitaryGroupMassFormula.QmBorderFull
theorem _root_.solution {t : ℕ} (p : Fin (t + 1)) (i : Fin t) : skip1 p i = p.succAbove i := by
  apply Fin.ext
  rw [val_succAbove]
  unfold skip1
  split_ifs with h1 h2 <;> first | rfl | (exact absurd h1 h2) | (exact absurd h2 h1) | omega
end PI.UnitaryGroupMassFormula.QmBorderFull
