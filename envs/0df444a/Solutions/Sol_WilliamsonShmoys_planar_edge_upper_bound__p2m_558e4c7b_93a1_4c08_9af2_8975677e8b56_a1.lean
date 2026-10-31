-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound__p2m_558e4c7b_93a1_4c08_9af2_8975677e8b56_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:25:25.265724+00:00
-- url     : https://prove2.me/submissions/6df0684e-64b1-4b32-8734-1a6191f0774f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exact_edge_count__p2m_ff2dc3a7_bc0c_4f6e_ac65_1b9f4eedc148_a1
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) : L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨N, hLN, hN, hCount⟩ :=
    WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_ff2dc3a7_bc0c_4f6e_ac65_1b9f4eedc148_a1 L hCard hL
  calc
    L.edgeSet.ncard ≤ N.edgeSet.ncard := Set.ncard_mono (SimpleGraph.edgeSet_mono hLN)
    _ = 3 * Fintype.card V - 6 := hCount.symm