-- Prove2me | solution 1 for PI.OkpW.norm_p_cp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:35:07.265509+00:00
-- url     : https://prove2.me/submissions/0ec166a0-1179-4ec0-9134-c2d41e50b179

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_OkpInert
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_NormLeOneOfIntegralInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open PI PI.OkpW
variable {p : ℕ} [hp : Fact p.Prime]
namespace PI.OkpW
theorem _root_.solution : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
  have : (p : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := (map_natCast _ p).symm
  rw [this, norm_algebraMap', Padic.norm_p]
end PI.OkpW
