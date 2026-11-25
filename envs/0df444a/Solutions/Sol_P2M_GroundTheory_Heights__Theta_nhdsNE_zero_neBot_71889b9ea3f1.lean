-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_nhdsNE_zero_neBot_71889b9ea3f1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:43:28.058372+00:00
-- url     : https://prove2.me/submissions/4ae6cdd5-7e2a-4749-9af0-3501ebd33f60

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_LocallyCompactField_Countability

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open MeasureTheory Measure Filter Topology Set
open scoped NNReal ENNReal Pointwise
variable {R : Type*} [Field R] [TopologicalSpace R] [IsTopologicalRing R]
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution (hR : ¬ DiscreteTopology R) : (𝓝[≠] (0 : R)).NeBot := by
  by_contra h
  rw [not_neBot, ← isOpen_singleton_iff_punctured_nhds] at h
  exact hR (discreteTopology_iff_isOpen_singleton_zero.mpr h)
end GroundTheory.Heights₂.Theta
