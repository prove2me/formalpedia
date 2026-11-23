-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_eventually_mul_mem_of_isCompact_2b6e19c23fce
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:39:36.367348+00:00
-- url     : https://prove2.me/submissions/b5afa46d-513a-426b-adc3-9d3aad059f6b

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
theorem _root_.solution {K N : Set R} (hK : IsCompact K) (hN : N ∈ 𝓝 (0 : R)) :
    ∀ᶠ u in 𝓝 (0 : R), ∀ w ∈ K, u * w ∈ N := by
  apply hK.eventually_forall_of_forall_eventually
  intro w _
  have h : Tendsto (fun z : R × R => z.1 * z.2) (𝓝 (0, w)) (𝓝 (0 * w)) :=
    continuous_mul.tendsto _
  rw [zero_mul] at h
  exact h.eventually_mem hN
end GroundTheory.Heights₂.Theta
