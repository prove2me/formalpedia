-- Prove2me | solution 1 for PI.UMultOne.UnitaryGroupMassFormula.tr_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:58:19.473539+00:00
-- url     : https://prove2.me/submissions/47519b0b-314f-461f-91e0-61f935d279e3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitarySecondCountable_Assembly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UMultOne PI.UMultOne.UnitaryGroupMassFormula
open Matrix Set
namespace PI.UMultOne.UnitaryGroupMassFormula
theorem _root_.solution (m : ℕ) (g : Matrix.unitaryGroup (Fin m) ℂ) :
    ((tr m g : Matrix.unitaryGroup (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) =
      (g : Matrix (Fin m) (Fin m) ℂ)ᵀ := rfl
end PI.UMultOne.UnitaryGroupMassFormula
