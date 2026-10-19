-- Prove2me | solution 1 for TwoDegenerateGraphs.exists_actualPairLayer_exclusion_parameters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/806f60b0-1d3d-483e-8458-54d7a8e7a2da

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_exists_entropy_exclusion_base
import Theorems.Thm_TwoDegenerateGraphs_exists_entropy_exclusion_depth

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution :
    ∃ baseSize depth : ℕ,
      4 ≤ baseSize ∧
      0 < depth ∧
      1 < (depth : ℝ) * (certifiedWindowWidth / 2) ∧
      ∀ layer : Fin depth,
        let layerSize :=
          Fintype.card (PairLayer baseSize layer.val)
        4 ≤ layerSize ∧
        empiricalEntropyError layerSize < entropySlack ∧
        (layerSize : ℝ) +
          3 * logTwo ((layerSize.choose 2 + 1 : ℕ) : ℝ) -
            entropySlack * (layerSize.choose 2 : ℝ) < -1 := by
  obtain ⟨baseSize, hbase, hbase_conditions⟩ :=
    exists_entropy_exclusion_base
  obtain ⟨depth, hdepth, hdepth_window⟩ :=
    exists_entropy_exclusion_depth
  refine ⟨baseSize, depth, hbase, hdepth, hdepth_window, ?_⟩
  intro layer
  dsimp
  have hsize :
      baseSize ≤ Fintype.card (PairLayer baseSize layer.val) :=
    pairLayer_card_ge_base baseSize layer.val hbase
  obtain ⟨herror, hfirst_moment⟩ :=
    hbase_conditions
      (Fintype.card (PairLayer baseSize layer.val)) hsize
  exact ⟨hbase.trans hsize, herror, hfirst_moment⟩
end TwoDegenerateGraphs
