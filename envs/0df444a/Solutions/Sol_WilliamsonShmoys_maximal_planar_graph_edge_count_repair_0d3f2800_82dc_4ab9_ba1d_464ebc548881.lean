-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count_repair_0d3f2800_82dc_4ab9_ba1d_464ebc548881
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T23:11:00.925689+00:00
-- url     : https://prove2.me/submissions/1588ba32-c9b1-49cc-a4ba-32b162b848a0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_completion_419a1fb2_144c_4e12_b921_930e8d46d3d3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) : 3 * Fintype.card V = L.edgeSet.ncard + 6 := by
  obtain ⟨M, hLM, hM, hCount⟩ :=
    WilliamsonShmoys.maximal_planar_edge_count_completion_419a1fb2_144c_4e12_b921_930e8d46d3d3
      L hL hCard
  have hEq : M = L := hMax M hLM hM
  simpa [hEq] using hCount