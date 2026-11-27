-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.holo_contDiffAt_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:29:37.060884+00:00
-- url     : https://prove2.me/submissions/bf2c78f0-d66a-4ff7-837f-f4ca80c718c6

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
    {f : EuclideanSpace ℂ (Fin n) → ℂ} (hΩ : IsOpen Ω) (hf : DifferentiableOn ℂ f Ω)
    {x : EuclideanSpace ℂ (Fin n)} (hx : x ∈ Ω) (k : ℕ) : ContDiffAt ℂ k f x := (contDiffOn_infty.1 (holoContDiff _ Ω f hΩ hf) k).contDiffAt (hΩ.mem_nhds hx)
end ReciprocityTheory.L2DbarEstimates.C
