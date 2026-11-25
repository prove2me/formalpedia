-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.moll_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:31:37.408668+00:00
-- url     : https://prove2.me/submissions/d6306196-134c-4064-82a2-6c21f9e07ad9

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_IntegralBumpProfOnePos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_integral_bumpProf
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_integral_bumpProf_one_pos

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
theorem _root_.solution (n : ℕ) {t : ℝ} (ht : 0 < t) : ∫ z : V n, moll n t z = 1 := by
  simp only [moll, mollProf]
  rw [integral_const_mul, integral_bumpProf ht, mollConst]
  have h1 := integral_bumpProf_one_pos n
  have h2 : t ^ (2 * n) ≠ 0 := pow_ne_zero _ ht.ne'
  field_simp
end ReciprocityTheory.L2DbarEstimates.C
