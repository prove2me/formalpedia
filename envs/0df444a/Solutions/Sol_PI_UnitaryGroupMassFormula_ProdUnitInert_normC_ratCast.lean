-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ProdUnitInert.normC_ratCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:41:25.889315+00:00
-- url     : https://prove2.me/submissions/eda245f6-6509-4a64-84cf-1e2fa291c9b9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertUnitProduct_NatCastNormLeOne

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
variable {p : ℕ} [Fact p.Prime]
namespace PI.UnitaryGroupMassFormula.ProdUnitInert
theorem _root_.solution (q : ℚ) : ‖(q : ℂ_[p])‖ = ‖(q : ℚ_[p])‖ := by
  have hc : (((q : ℚ_[p]) : PadicAlgCl p) : ℂ_[p]) = (q : ℂ_[p]) := by
    simp only [PadicComplex.coe_eq, map_ratCast]
  rw [← hc, PadicComplex.norm_extends, PadicAlgCl.norm_extends]
end PI.UnitaryGroupMassFormula.ProdUnitInert
