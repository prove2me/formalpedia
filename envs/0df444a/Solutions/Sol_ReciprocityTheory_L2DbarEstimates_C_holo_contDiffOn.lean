-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.holo_contDiffOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:27:31.385899+00:00
-- url     : https://prove2.me/submissions/1cddb0ed-32d0-4468-be6c-ebcf78480456

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloContDiffStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_IntegralMollProfBall
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_MollifyEqConvolution
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_holoSmooth

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
open scoped ENNReal ContDiff Convolution
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution {n : ℕ} {Ω : Set (EuclideanSpace ℂ (Fin n))}
    {f : EuclideanSpace ℂ (Fin n) → ℂ} (hΩ : IsOpen Ω) (hf : DifferentiableOn ℂ f Ω) :
    ContDiffOn ℝ ∞ f Ω := by
  exact holoSmooth n Ω f hΩ hf
end ReciprocityTheory.L2DbarEstimates.C
