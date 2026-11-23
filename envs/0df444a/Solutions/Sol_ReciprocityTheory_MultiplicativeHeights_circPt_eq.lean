-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.circPt_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:01:35.412711+00:00
-- url     : https://prove2.me/submissions/88caf197-1e0a-4195-bbab-4bda356c8858

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Polynomial Real
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (t : ℝ) : circPt t = circleMap 0 1 (2 * π * t) := by
  rw [circleMap_zero, circPt]; push_cast; ring_nf
end ReciprocityTheory.MultiplicativeHeights
