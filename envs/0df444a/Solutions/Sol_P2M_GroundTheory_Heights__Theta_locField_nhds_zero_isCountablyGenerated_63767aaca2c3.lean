-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_locField_nhds_zero_isCountablyGenerated_63767aaca2c3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:58:48.887521+00:00
-- url     : https://prove2.me/submissions/d913a0fa-cbe1-44c3-8b02-a4d68f0f5339

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_LocallyCompactField_Countability
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_eventually_mul_mem_of_isCompact_2b6e19c23fce
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_exists_tendsto_pow_zero_a94ec10e85d3

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
variable [LocallyCompactSpace R] [T2Space R]
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution (hR : ¬ DiscreteTopology R) :
    (𝓝 (0 : R)).IsCountablyGenerated := by
  obtain ⟨t, ht0, ht⟩ := exists_tendsto_pow_zero hR
  obtain ⟨W, hWc, hWn⟩ : ∃ W : Set R, IsCompact W ∧ W ∈ 𝓝 (0 : R) := exists_compact_mem_nhds 0
  have hb : (𝓝 (0 : R)).HasBasis (fun _ : ℕ => True) (fun n => (fun x => t ^ n * x) '' W) := by
    refine ⟨fun U => ⟨fun hU => ?_, ?_⟩⟩
    · obtain ⟨n, hn⟩ := (ht.eventually (eventually_mul_mem_of_isCompact hWc hU)).exists
      exact ⟨n, trivial, by rintro _ ⟨w, hw, rfl⟩; exact hn w hw⟩
    · rintro ⟨n, -, hn⟩
      apply mem_of_superset _ hn
      have h := (mulLeftAddEquiv (t ^ n) (pow_ne_zero n ht0)).toHomeomorph.isOpenMap.image_mem_nhds
        hWn
      have e1 : ((mulLeftAddEquiv (t ^ n) (pow_ne_zero n ht0)).toHomeomorph : R → R) =
          fun x => t ^ n * x := rfl
      rw [e1] at h
      simpa only [mul_zero] using h
  exact hb.isCountablyGenerated
end GroundTheory.Heights₂.Theta
