-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count_strict_augmentation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T16:56:58.900763+00:00
-- url     : https://prove2.me/submissions/9e705c5f-59a9-4179-8974-baa75ff4ac63

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_supergraph_with_no_drawable_extension
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_for_strict_augmentation_ff597491

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hTdraw : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hCard : 3 ≤ Fintype.card V)
    (hSparse : T.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ U : SimpleGraph V, T ≤ U ∧ U ≠ T ∧ WilliamsonShmoys.HasPlanarDrawingOn U := by
  obtain ⟨U, hTU, hUdraw, hUmax⟩ :=
    WilliamsonShmoys.drawable_supergraph_with_no_drawable_extension T hTdraw hCard
  have hUcount :=
    WilliamsonShmoys.maximal_drawable_graph_edge_count_for_strict_augmentation_ff597491
      U hUdraw hCard hUmax
  refine ⟨U, hTU, ?_, hUdraw⟩
  intro hUT
  have hcounts : U.edgeSet.ncard = T.edgeSet.ncard := by
    simpa [hUT]
  omega