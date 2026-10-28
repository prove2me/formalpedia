-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_has_triangulation_completion_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T06:55:43.135065+00:00
-- url     : https://prove2.me/submissions/dcb47b26-5b26-450f-9427-bd35ed8702a4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_edge_maximal_completion
import Theorems.Thm_WilliamsonShmoys_edge_maximal_drawable_graph_edge_count

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hV : 3 <= Fintype.card V) :
    ∃ U : SimpleGraph V,
      (∀ {u v}, T.Adj u v → U.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn U ∧
      U.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨U, hTU, hdrawU, hmax⟩ :=
    WilliamsonShmoys.drawable_graph_has_edge_maximal_completion T hdraw hV
  refine ⟨U, hTU, hdrawU, ?_⟩
  exact WilliamsonShmoys.edge_maximal_drawable_graph_edge_count U hdrawU hV hmax