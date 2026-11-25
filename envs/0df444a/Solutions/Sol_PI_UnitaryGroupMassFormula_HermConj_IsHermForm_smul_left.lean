-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.HermConj.IsHermForm.smul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:40:07.24655+00:00
-- url     : https://prove2.me/submissions/e237d26d-8be4-4fc1-9ce7-4213f3df51e6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianDiagonalization_HermDiag
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianDiagonalization_ExistsOrthogonalFamily

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.HermConj
open Matrix
variable {E : Type} [Field E]
variable {σ : E →+* E} {V : Type} [AddCommGroup V] [Module E V] {h : V → V → E}
namespace PI.UnitaryGroupMassFormula.HermConj
namespace IsHermForm
theorem _root_.solution (hh : IsHermForm σ h) (a : E) (x y : V) :
    h (a • x) y = σ a * h x y := by
  rw [hh.herm y (a • x), hh.smul, map_mul, ← hh.herm y x]
end IsHermForm
end PI.UnitaryGroupMassFormula.HermConj
