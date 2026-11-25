-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.divBy_of_mul_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:41:54.830447+00:00
-- url     : https://prove2.me/submissions/818216b0-b539-4277-8e79-54a27d100c79

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divBy_mul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralPS_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {x : K} {f g : PowerSeries K} (hf : IntegralPS f)
    (h0 : ‖constantCoeff f‖ = 1) (h : DivBy x (f * g)) : DivBy x g := by
  have hf0 : constantCoeff f ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at h0
    exact zero_ne_one h0
  have e : g = f⁻¹ * (f * g) := by rw [← mul_assoc, PowerSeries.inv_mul_cancel _ hf0, one_mul]
  rw [e]
  exact divBy_mul_left (integralPS_inv hf h0) h
end ReciprocityTheory.ChartRestriction.L1
