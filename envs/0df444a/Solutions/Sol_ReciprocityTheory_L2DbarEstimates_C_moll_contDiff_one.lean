-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.moll_contDiff_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:13.40138+00:00
-- url     : https://prove2.me/submissions/fa48fafb-a824-41be-92c9-adcde963d19e

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_IntegralBumpProfOnePos
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_RegConv
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_moll_contDiff


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
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution (n : ℕ) (t : ℝ) : ContDiff ℝ 1 (moll n t) := (moll_contDiff n t).of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
end ReciprocityTheory.L2DbarEstimates.C
