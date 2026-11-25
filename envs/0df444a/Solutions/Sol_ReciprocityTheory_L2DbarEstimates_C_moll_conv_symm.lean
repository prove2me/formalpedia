-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.moll_conv_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:05:36.11885+00:00
-- url     : https://prove2.me/submissions/839bb953-dbda-48ba-b055-5927dc4adae2

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_MeasurableEmbeddingRotAbout
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_RegConv
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_RegIndep

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
theorem _root_.solution (n : ℕ) (s t : ℝ) (x y : V n) :
    ∫ w, moll n s (x - w) * moll n t (w - y) = ∫ w, moll n t (x - w) * moll n s (w - y) := by
  calc ∫ w, moll n s (x - w) * moll n t (w - y)
      = ∫ w, moll n s (x - (x + y - w)) * moll n t ((x + y - w) - y) :=
        (integral_sub_left_eq_self (fun w => moll n s (x - w) * moll n t (w - y)) volume
          (x + y)).symm
    _ = ∫ w, moll n t (x - w) * moll n s (w - y) := by
        congr 1; funext w
        rw [mul_comm]
        congr 2 <;> abel
end ReciprocityTheory.L2DbarEstimates.C
