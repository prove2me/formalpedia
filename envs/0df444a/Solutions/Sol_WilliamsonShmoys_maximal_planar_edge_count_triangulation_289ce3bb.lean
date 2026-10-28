-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_triangulation_289ce3bb
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T14:59:04.918873+00:00
-- url     : https://prove2.me/submissions/3da75bfb-8640-457b-ae2f-50825c6e57d8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_triangulating_supergraph

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ K : SimpleGraph V, N ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = N) :
    N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hNK, hK, hcount⟩ :=
    WilliamsonShmoys.drawable_graph_has_triangulating_supergraph N hV hN
  have hKN : K = N := hmax K hNK hK
  rw [hKN] at hcount
  exact hcount