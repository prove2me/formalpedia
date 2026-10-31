-- Prove2me | solution 2 for WilliamsonShmoys.maximal_drawable_supergraph_edge_count__p2m_ba617e25_272f_480b_8c9f_e5a82d8e4502_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:31:57.81801+00:00
-- url     : https://prove2.me/submissions/540bc037-ce0a-420e-a866-cbc20475e76c

import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_drawing_repair_d02dec5c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (S : SimpleGraph V) (hS : WilliamsonShmoys.HasPlanarDrawingOn S) (hCard : 3 ≤ Fintype.card V) (hMax : ∀ T : SimpleGraph V, S ≤ T → WilliamsonShmoys.HasPlanarDrawingOn T → T = S) : S.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.edge_count_of_maximal_planar_drawing_repair_d02dec5c S hS hCard hMax
