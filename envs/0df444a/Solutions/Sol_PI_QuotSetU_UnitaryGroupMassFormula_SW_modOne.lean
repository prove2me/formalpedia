-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.modOne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:34.336255+00:00
-- url     : https://prove2.me/submissions/5e620d59-127f-4b5e-8596-d79de5c3f9a6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_IsClosedS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_IsCompactInterUnitBox

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW
open PI PI.QuotSetU
variable {m : ℕ} {G : Set (Matrix (Fin m) (Fin m) ℂ)} {D : Matrix (Fin m) (Fin m) ℂ → ℝ}
namespace PI.QuotSetU.UnitaryGroupMassFormula.SW
theorem _root_.solution (hG : IsMatGroup G) (hD : ModProps G D) : D 1 = 1 := by
  have h1 : (1 : Matrix (Fin m) (Fin m) ℂ) ∈ G := hG.2.1
  have hpos := hD.1 1 h1
  have hm := hD.2.1 1 h1 1 h1
  rw [mul_one] at hm
  exact mul_left_cancel₀ hpos.ne' (hm.symm.trans (mul_one (D 1)).symm)
end PI.QuotSetU.UnitaryGroupMassFormula.SW
