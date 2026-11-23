-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.ZI.inverse_eA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:56:51.906829+00:00
-- url     : https://prove2.me/submissions/5352db0d-3e70-4ca6-b5a4-a2b378e91737

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZIterA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZIterB
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_ZI_eA_mul_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost PI.UnitaryGroupMassFormula.UsCost.ZI
variable (s : ℕ)
namespace PI.UnitaryGroupMassFormula.UsCost.ZI
theorem _root_.solution {Z : Fin s → Fin s → ℂ} (h : (Matrix.of Z).det ≠ 0) :
    Ring.inverse (eA s Z) = eA s (invF s Z) := by
  exact Ring.inverse_unit ⟨eA s Z, eA s (invF s Z), (eA_mul_inv s h).1, (eA_mul_inv s h).2⟩
end PI.UnitaryGroupMassFormula.UsCost.ZI
