-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_locField_sigmaCompactSpace_3d78a5bf45ec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:58:52.890797+00:00
-- url     : https://prove2.me/submissions/5652f8f2-80ce-45fd-8d95-eae8e21a78c5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_LocallyCompactField_Countability
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
theorem _root_.solution (hR : ¬ DiscreteTopology R) : SigmaCompactSpace R := by
  obtain ⟨t, ht0, ht⟩ := exists_tendsto_pow_zero hR
  obtain ⟨W, hWc, hWn⟩ : ∃ W : Set R, IsCompact W ∧ W ∈ 𝓝 (0 : R) := exists_compact_mem_nhds 0
  refine ⟨⟨fun n => (fun x => (t ^ n)⁻¹ * x) '' W,
    fun n => hWc.image (continuous_const.mul continuous_id), ?_⟩⟩
  apply eq_univ_of_forall
  intro x
  have h : Tendsto (fun n : ℕ => t ^ n * x) atTop (𝓝 0) := by
    have := ht.mul_const x
    rwa [zero_mul] at this
  obtain ⟨n, hn⟩ := (h.eventually_mem hWn).exists
  exact mem_iUnion.mpr ⟨n, t ^ n * x, hn, inv_mul_cancel_left₀ (pow_ne_zero n ht0) x⟩
end GroundTheory.Heights₂.Theta
