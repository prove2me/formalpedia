-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.measurePreserving_rotAbout
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:14:08.55038+00:00
-- url     : https://prove2.me/submissions/3178f8a0-f2f7-4a50-bb28-170ff89808b2

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_Circle
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_MeasurableEmbeddingRotAbout
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_measurePreserving_smul_unit


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
theorem _root_.solution {n : ℕ} (c : V n) {a : ℂ} (ha : ‖a‖ = 1) :
    MeasurePreserving (rotAbout c a) volume volume :=
  (measurePreserving_add_left volume c).comp
    ((measurePreserving_smul_unit a ha).comp (measurePreserving_sub_right volume c))
end ReciprocityTheory.L2DbarEstimates.C
