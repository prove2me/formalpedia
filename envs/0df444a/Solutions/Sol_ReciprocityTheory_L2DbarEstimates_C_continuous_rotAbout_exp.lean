-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.continuous_rotAbout_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:02:37.970113+00:00
-- url     : https://prove2.me/submissions/7177319d-1bda-4bd1-b9dd-11ff33432ae4

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_Circle
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_MeasurableEmbeddingRotAbout

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
theorem _root_.solution {n : ℕ} (c : V n) :
    Continuous (fun p : ℝ × V n => rotAbout c (Complex.exp ((p.1 : ℂ) * I)) p.2) := by
  unfold rotAbout; fun_prop
end ReciprocityTheory.L2DbarEstimates.C
