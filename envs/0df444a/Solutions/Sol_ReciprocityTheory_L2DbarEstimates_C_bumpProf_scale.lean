-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.bumpProf_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:02:08.698675+00:00
-- url     : https://prove2.me/submissions/6ca0cf57-56c2-4ac4-ab27-53b747d0e022

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_IntegralBumpProfOnePos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution {t : ℝ} (ht : 0 < t) (z : V n) : bumpProf t ‖z‖ = bumpProf 1 ‖t⁻¹ • z‖ := by
  simp only [bumpProf, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht, div_one]
  congr 1
  ring
end ReciprocityTheory.L2DbarEstimates.C
