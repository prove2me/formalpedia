-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.HermConj.IsHermForm.add_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:40:04.697736+00:00
-- url     : https://prove2.me/submissions/ae097d71-e909-4a82-ac71-6ece20fe46b7

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
theorem _root_.solution (hh : IsHermForm σ h) (x y z : V) :
    h (x + y) z = h x z + h y z := by
  rw [hh.herm z (x + y), hh.add, map_add, ← hh.herm z x, ← hh.herm z y]
end IsHermForm
end PI.UnitaryGroupMassFormula.HermConj
