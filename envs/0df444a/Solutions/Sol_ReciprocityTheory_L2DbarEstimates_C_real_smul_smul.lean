-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.real_smul_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:02:24.860558+00:00
-- url     : https://prove2.me/submissions/f94a6cb6-e091-48df-aef5-deb499fb2e01

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutA

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
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution (t : ℝ) (μ : ℂ) (e : V n) : t • (μ • e) = ((t : ℂ) * μ) • e := by
  rw [← Complex.coe_smul, smul_smul]
end ReciprocityTheory.L2DbarEstimates.C
