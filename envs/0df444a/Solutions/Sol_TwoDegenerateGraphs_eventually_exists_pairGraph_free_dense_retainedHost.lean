-- Prove2me | solution 1 for TwoDegenerateGraphs.eventually_exists_pairGraph_free_dense_retainedHost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/e175831b-ee3f-40da-aed9-00c8ae0c3093

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_exists_hammingRetention_outside_event
import Theorems.Thm_TwoDegenerateGraphs_exists_actualPairLayer_exclusion_parameters
import Theorems.Thm_TwoDegenerateGraphs_manuscriptSamplingFailureBound_tendsto_zero
import Theorems.Thm_TwoDegenerateGraphs_manuscriptSamplingFailureEvent_real_le
import Theorems.Thm_TwoDegenerateGraphs_pairGraphOverFin_free_of_manuscript_exclusion

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution :
    ∃ baseSize depth : ℕ,
      4 ≤ baseSize ∧
      0 < depth ∧
      1 < (depth : ℝ) * (certifiedWindowWidth / 2) ∧
      ∀ᶠ dimension : ℕ in Filter.atTop,
        ∃ retained : Set (Bool × HammingWord dimension),
          (pairGraphOverFin baseSize depth).Free
              (retainedHammingHost dimension
                (manuscriptHammingRadius dimension) retained) ∧
          hammingRetainedVertexCount dimension retained <
            3 * hammingRetentionProbability dimension *
              ((2 ^ dimension : ℕ) : ℝ) ∧
          hammingExpectedRetainedEdgeCount dimension
              (manuscriptHammingRadius dimension) / 2 ≤
            hammingRetainedEdgeCount dimension
              (manuscriptHammingRadius dimension) retained := by
  obtain ⟨baseSize, depth, hbase, hdepth, hdepth_window, hlayers⟩ :=
    exists_actualPairLayer_exclusion_parameters
  let layerSizes : Fin depth → ℕ := fun layer =>
    Fintype.card (PairLayer baseSize layer.val)
  have hparents : ∀ layer, 4 ≤ layerSizes layer :=
    fun layer => (hlayers layer).1
  have hfirst_moment :
      ∀ layer,
        (layerSizes layer : ℝ) +
          3 * logTwo
            (((layerSizes layer).choose 2 + 1 : ℕ) : ℝ) -
            entropySlack * ((layerSizes layer).choose 2 : ℝ) < -1 :=
    fun layer => (hlayers layer).2.2
  have hsmall :
      ∀ᶠ dimension : ℕ in Filter.atTop,
        manuscriptSamplingFailureBound depth dimension < 1 :=
    (tendsto_order.1
      (manuscriptSamplingFailureBound_tendsto_zero depth)).2
        1 (by norm_num)
  refine ⟨baseSize, depth, hbase, hdepth, hdepth_window, ?_⟩
  filter_upwards [hsmall, Filter.eventually_gt_atTop 0] with dimension
    hbound hdimension
  obtain ⟨retained, houtside⟩ :=
    exists_hammingRetention_outside_event dimension
      (manuscriptSamplingFailureEvent layerSizes dimension)
      ((manuscriptSamplingFailureEvent_real_le layerSizes
        hdimension hparents hfirst_moment).trans_lt hbound)
  have hexclusion :
      ∀ (side : Bool) (layer : Fin depth),
        retained ∉
          badPairLayerRetentionEvent
            (layerSizes layer) dimension side
              (midpointBeta - entropySlack) := by
    intro side layer hbad
    exact houtside (Or.inl (Or.inl (Set.mem_iUnion.mpr
      ⟨side, Set.mem_iUnion.mpr ⟨layer, hbad⟩⟩)))
  have hvertices :
      hammingRetainedVertexCount dimension retained <
        3 * hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ) :=
    lt_of_not_ge fun hlarge => houtside (Or.inl (Or.inr hlarge))
  have hedges :
      hammingExpectedRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension) / 2 ≤
        hammingRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension) retained :=
    le_of_not_gt fun hlow => houtside (Or.inr hlow)
  exact ⟨retained,
    pairGraphOverFin_free_of_manuscript_exclusion
      hbase hdimension hdepth_window retained hexclusion
      (fun layer => (hlayers layer).2.1),
    hvertices, hedges⟩
end TwoDegenerateGraphs
