-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_edge_count_3v_minus_6
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:34:56.865237+00:00
-- url     : https://prove2.me/submissions/4bcdea98-4150-4e1d-8000-97d6ac078bf4

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_exists
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    Exists fun K : SimpleGraph V =>
      H <= K /\
      WilliamsonShmoys.HasPlanarDrawingOn K /\
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hKdraw, hmax⟩ :=
    WilliamsonShmoys.maximal_drawable_supergraph_exists H hH
  refine ⟨K, hHK, hKdraw, ?_⟩
  exact WilliamsonShmoys.maximal_drawable_supergraph_edge_count
    K hV hKdraw (fun L hKL hLdraw => hmax L hKL hLdraw)