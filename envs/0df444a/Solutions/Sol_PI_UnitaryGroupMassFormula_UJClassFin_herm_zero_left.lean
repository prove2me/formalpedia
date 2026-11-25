-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassFin.herm_zero_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:44:37.725029+00:00
-- url     : https://prove2.me/submissions/2d87e7a7-3e7e-43ac-8c2c-bee2f75be049

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_ClassFiniteOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_HermSingleLeft

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField
open scoped ComplexOrder
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassFin
open PI.HermLatFin
variable {E : Type} [Field E] {M : ℕ} (σ : E →+* E) (J : Matrix (Fin M) (Fin M) E)
namespace PI.UnitaryGroupMassFormula.UJClassFin
theorem _root_.solution (y : Fin M → E) : herm σ J 0 y = 0 := by
  simp [herm]
end PI.UnitaryGroupMassFormula.UJClassFin
