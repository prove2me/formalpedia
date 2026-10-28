-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_triangulation_for_maximal_edge_count_e6187372_db43_4b05_9178_6f8ead22bdbc
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T12:50:32.915411+00:00
-- url     : https://prove2.me/submissions/b79d0a09-298e-4960-8b1d-aa7dab244e98
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_has_maximal_extension_e6187372_db43_4b05_9178_6f8ead22bdbc
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_e6187372_db43_4b05_9178_6f8ead22bdbc
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨N, hMN, hN, hMax⟩ :=
    WilliamsonShmoys.planar_supergraph_has_maximal_extension_e6187372_db43_4b05_9178_6f8ead22bdbc M hM
  exact ⟨N, hMN, hN,
    WilliamsonShmoys.maximal_planar_drawing_edge_count_e6187372_db43_4b05_9178_6f8ead22bdbc N hV hN hMax⟩