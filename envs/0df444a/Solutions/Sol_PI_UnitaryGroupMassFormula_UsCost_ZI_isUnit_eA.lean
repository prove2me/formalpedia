-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.ZI.isUnit_eA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:56:51.951499+00:00
-- url     : https://prove2.me/submissions/077ee5e2-68d1-4575-8d86-bf85f7cc3673

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
theorem _root_.solution {Z : Fin s → Fin s → ℂ} (h : (Matrix.of Z).det ≠ 0) : IsUnit (eA s Z) :=
  ⟨⟨eA s Z, eA s (invF s Z), (eA_mul_inv s h).1, (eA_mul_inv s h).2⟩, rfl⟩
end PI.UnitaryGroupMassFormula.UsCost.ZI
