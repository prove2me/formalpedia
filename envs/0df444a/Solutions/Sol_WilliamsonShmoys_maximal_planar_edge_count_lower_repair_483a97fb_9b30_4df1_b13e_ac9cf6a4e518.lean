-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_repair_483a97fb_9b30_4df1_b13e_ac9cf6a4e518
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T11:15:08.540194+00:00
-- url     : https://prove2.me/submissions/c7439a0e-4c9e-4c69-b62e-4574805a8f5b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulating_supergraph_repair_a3780995_02f0_4c2f_a98c_6e5f167c3de5

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hNdraw : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hNmax : ∀ P : SimpleGraph V, N ≤ P → WilliamsonShmoys.HasPlanarDrawingOn P → P = N)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ N.edgeSet.ncard + 6 := by
  obtain ⟨P, hNP, hPdraw, hPcard⟩ :=
    WilliamsonShmoys.planar_graph_has_triangulating_supergraph_repair_a3780995_02f0_4c2f_a98c_6e5f167c3de5
      N hNdraw hCard
  have hPN : P = N := hNmax P hNP hPdraw
  rw [← hPN]
  exact le_of_eq hPcard.symm