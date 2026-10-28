-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_dense_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:29:55.308907+00:00
-- url     : https://prove2.me/submissions/1038889e-1e87-49ce-961b-147b8129c331
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_dense_ext_for_planar_dense_extension_v4
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_lower_bound_3n6_for_planar_dense_extension_v4

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    exists P : SimpleGraph V, N <= P /\ WilliamsonShmoys.HasPlanarDrawingOn P /\
      3 * Fintype.card V - 6 <= P.edgeSet.ncard := by
  obtain ⟨P, hNP, hP, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph_dense_ext_for_planar_dense_extension_v4 N hN
  refine ⟨P, hNP, hP, ?_⟩
  exact WilliamsonShmoys.maximal_drawable_graph_edge_lower_bound_3n6_for_planar_dense_extension_v4 P hV hP hMax