-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.integral_bumpProf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:13:58.039859+00:00
-- url     : https://prove2.me/submissions/e34dda61-33ea-41b3-80c9-f8a90f82c6e4

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_IntegralBumpProfOnePos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_finrank_V
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_bumpProf_scale

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
theorem _root_.solution {t : ℝ} (ht : 0 < t) :
    ∫ z : V n, bumpProf t ‖z‖ = t ^ (2 * n) * ∫ z : V n, bumpProf 1 ‖z‖ := by
  simp_rw [bumpProf_scale ht]
  rw [Measure.integral_comp_inv_smul_of_nonneg volume (fun z : V n => bumpProf 1 ‖z‖) ht.le,
    finrank_V, smul_eq_mul]
end ReciprocityTheory.L2DbarEstimates.C
