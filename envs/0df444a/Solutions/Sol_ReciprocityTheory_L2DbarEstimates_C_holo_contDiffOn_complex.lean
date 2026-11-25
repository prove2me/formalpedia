-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.holo_contDiffOn_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:55:39.765448+00:00
-- url     : https://prove2.me/submissions/6e101e4c-152c-40c5-85f9-8d179ea3fe56

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExistsClmOfI
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloContDiffAtComplex
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_holoContDiff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open Metric Set Filter Topology Complex
open scoped ContDiff
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution {n : ℕ} {Ω : Set (EuclideanSpace ℂ (Fin n))}
    {f : EuclideanSpace ℂ (Fin n) → ℂ} (hΩ : IsOpen Ω) (hf : DifferentiableOn ℂ f Ω) :
    ContDiffOn ℂ ∞ f Ω := holoContDiff _ Ω f hΩ hf
end ReciprocityTheory.L2DbarEstimates.C
