-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_extension_for_edge_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:40:06.341056+00:00
-- url     : https://prove2.me/submissions/17b419a4-11d5-4302-acf1-66ce3b0465bc

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_of_finite_graph_property
import Theorems.Thm_WilliamsonShmoys_planar_drawing_mono

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hconn : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G.edgeSet.ncard <= H.edgeSet.ncard ∧
      H.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ H' : SimpleGraph V, H < H' → ¬ WilliamsonShmoys.HasPlanarDrawingOn H' := by
  have hdown : ∀ A B : SimpleGraph V,
      A ≤ B → WilliamsonShmoys.HasPlanarDrawingOn B →
        WilliamsonShmoys.HasPlanarDrawingOn A := by
    intro A B hAB hB
    exact WilliamsonShmoys.planar_drawing_mono hAB hB
  obtain ⟨H, hGH, hcard, hH, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_supergraph_of_finite_graph_property
      (fun K : SimpleGraph V => WilliamsonShmoys.HasPlanarDrawingOn K)
      hdown G hG
  exact ⟨H, hcard, hconn.mono hGH, hH, hmax⟩