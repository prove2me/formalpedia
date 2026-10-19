-- Prove2me | solution 1 for TwoDegenerateGraphs.eventually_expectedRetainedEdge_le_extremalNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/06e33a7b-35de-4506-b14c-ba71cea6abd7

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_free_map_of_no_isolated
import Theorems.Thm_TwoDegenerateGraphs_hammingRetainedEdgeCount_eq_edgeFinset_card
import Theorems.Thm_TwoDegenerateGraphs_eventually_exists_pairGraph_free_dense_retainedHost
import Theorems.Thm_TwoDegenerateGraphs_pairGraphOverFin_forall_exists_adj
import Theorems.Thm_TwoDegenerateGraphs_retainedVertex_card_le_manuscriptVertexCount

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
open Classical
namespace TwoDegenerateGraphs
theorem _root_.solution :
    ∃ baseSize depth : ℕ,
      4 ≤ baseSize ∧
      0 < depth ∧
      1 < (depth : ℝ) * (certifiedWindowWidth / 2) ∧
      ∀ᶠ dimension : ℕ in Filter.atTop,
        hammingExpectedRetainedEdgeCount dimension
            (manuscriptHammingRadius dimension) / 2 ≤
          (SimpleGraph.extremalNumber
            (manuscriptVertexCount dimension)
            (pairGraphOverFin baseSize depth) : ℝ) := by
  obtain ⟨baseSize, depth, hbase, hdepth,
    hdepth_window, hhosts⟩ :=
    eventually_exists_pairGraph_free_dense_retainedHost
  refine ⟨baseSize, depth, hbase, hdepth, hdepth_window, ?_⟩
  filter_upwards [hhosts] with dimension hhost
  obtain ⟨retained, hfree, hvertices, hedges⟩ := hhost
  have hcard :=
    retainedVertex_card_le_manuscriptVertexCount
      dimension retained hvertices
  have hembedding :
      Nonempty (retained ↪ Fin (manuscriptVertexCount dimension)) := by
    apply Function.Embedding.nonempty_of_card_le
    simpa using hcard
  obtain ⟨embedding⟩ := hembedding
  let paddedHost : SimpleGraph (Fin (manuscriptVertexCount dimension)) :=
    (retainedHammingHost dimension
      (manuscriptHammingRadius dimension) retained).map embedding
  have hpadded_free :
      (pairGraphOverFin baseSize depth).Free paddedHost := by
    exact CompactnessConjecture.free_map_of_no_isolated
      (pairGraphOverFin baseSize depth)
      (pairGraphOverFin_forall_exists_adj baseSize depth hbase hdepth)
      embedding hfree
  have hpadded_edges :
      paddedHost.edgeFinset.card ≤
        SimpleGraph.extremalNumber
          (manuscriptVertexCount dimension)
          (pairGraphOverFin baseSize depth) := by
    simpa using
      (SimpleGraph.card_edgeFinset_le_extremalNumber hpadded_free)
  calc
    hammingExpectedRetainedEdgeCount dimension
        (manuscriptHammingRadius dimension) / 2 ≤
      hammingRetainedEdgeCount dimension
        (manuscriptHammingRadius dimension) retained := hedges
    _ = ((retainedHammingHost dimension
        (manuscriptHammingRadius dimension) retained).edgeFinset.card : ℝ) :=
      hammingRetainedEdgeCount_eq_edgeFinset_card
        dimension (manuscriptHammingRadius dimension) retained
    _ = (paddedHost.edgeFinset.card : ℝ) := by
      congr 1
      exact (SimpleGraph.card_edgeFinset_map embedding
        (retainedHammingHost dimension
          (manuscriptHammingRadius dimension) retained)).symm
    _ ≤ (SimpleGraph.extremalNumber
        (manuscriptVertexCount dimension)
        (pairGraphOverFin baseSize depth) : ℝ) := by
      exact_mod_cast hpadded_edges
end TwoDegenerateGraphs
