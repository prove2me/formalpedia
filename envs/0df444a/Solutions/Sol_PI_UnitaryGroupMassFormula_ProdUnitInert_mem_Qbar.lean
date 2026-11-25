-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ProdUnitInert.mem_Qbar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:41:21.623028+00:00
-- url     : https://prove2.me/submissions/105ae7b1-af89-4339-9f32-77cd60d116da

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ProdUnitInert
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertUnitProduct_NatCastNormLeOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertUnitProduct_ExistsRatCoords
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertUnitProduct_MemQbar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ProdUnitInert
open PI.ProdUnitInert
namespace PI.UnitaryGroupMassFormula.ProdUnitInert
theorem _root_.solution {E : Type} [Field E] [NumberField E] (φ₀ : E →+* ℂ) (e : E) :
    φ₀ e ∈ Qbar := by
  rw [Qbar, mem_algebraicClosure_iff']
  exact (Algebra.IsIntegral.isIntegral (R := ℚ) e).map φ₀.toRatAlgHom
end PI.UnitaryGroupMassFormula.ProdUnitInert
