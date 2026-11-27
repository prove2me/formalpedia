-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.isTest_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:29:41.340196+00:00
-- url     : https://prove2.me/submissions/585379f3-5429-44ce-bb54-f9feec54364f

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement

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
theorem _root_.solution {n : ℕ} (Ω : Set (V n)) : IsTest Ω (fun _ => 0) :=
  ⟨contDiff_const, HasCompactSupport.zero, by simp [tsupport]⟩
end ReciprocityTheory.L2DbarEstimates.C
