-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:06:51.374846+00:00
-- url     : https://prove2.me/submissions/147186bb-c497-4a64-bb6b-c4f917dc9d15

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloContDiffAtComplex
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_holo_contDiffOn_complex


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution (n : ℕ) (g : V n → ℂ) (U : Set (V n)) (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) : ContDiffOn ℂ ∞ g U := C.holo_contDiffOn_complex hU hg
end ReciprocityTheory.L2DbarEstimates
