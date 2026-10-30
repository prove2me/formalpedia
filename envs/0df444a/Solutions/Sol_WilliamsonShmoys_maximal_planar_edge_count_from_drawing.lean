-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_from_drawing
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T08:23:44.151296+00:00
-- url     : https://prove2.me/submissions/958edd01-a3c2-488c-8197-780628ffc659

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation_edge_count_acab26a7

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hKplanar, hKcount⟩ :=
    WilliamsonShmoys.planar_supergraph_triangulation_edge_count_acab26a7 H hV hH
  have hKH : K = H := hmax K hHK hKplanar
  rw [hKH] at hKcount
  exact hKcount