-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmBorderFull.comp_skip1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:41:48.850933+00:00
-- url     : https://prove2.me/submissions/00c77a4b-33f9-49fb-b706-11e1e043b35b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_SkipOneEqSuccAbove
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_skip_one_eq_succAbove

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
theorem _root_.solution {α : Type*} {t : ℕ} (f : Fin (t + 1) → α) (p : Fin (t + 1)) :
    f ∘ skip1 p = f ∘ p.succAbove := by
  funext i
  exact congrArg f (skip_one_eq_succAbove p i)
end PI.UnitaryGroupMassFormula.QmBorderFull
