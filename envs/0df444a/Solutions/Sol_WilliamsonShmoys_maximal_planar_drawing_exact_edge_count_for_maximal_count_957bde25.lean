-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_exact_edge_count_for_maximal_count_957bde25
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T20:39:31.055754+00:00
-- url     : https://prove2.me/submissions/93021442-4f93-4e4b-8298-7f0ba477b727

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulated_supergraph_fixed_vertices

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hKmax : forall M : SimpleGraph V, K <= M -> WilliamsonShmoys.HasPlanarDrawingOn M -> M = K) :
    (K.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨M, hKM, hMdraw, hMcount⟩ :=
    WilliamsonShmoys.planar_drawing_has_triangulated_supergraph_fixed_vertices K hK hV
  have hMK : M = K := hKmax M hKM hMdraw
  rw [← hMK]
  exact hMcount