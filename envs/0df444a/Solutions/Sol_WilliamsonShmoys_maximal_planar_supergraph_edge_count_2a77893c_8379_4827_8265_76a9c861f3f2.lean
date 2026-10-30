-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_edge_count_2a77893c_8379_4827_8265_76a9c861f3f2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T12:42:59.494063+00:00
-- url     : https://prove2.me/submissions/bf5b4a5c-65cb-40ea-90c9-bb4a3140eafe

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation_for_maximal_edge_count_e6187372_db43_4b05_9178_6f8ead22bdbc

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N = M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨N, hMN, hN, hcount⟩ :=
    WilliamsonShmoys.planar_supergraph_triangulation_for_maximal_edge_count_e6187372_db43_4b05_9178_6f8ead22bdbc
      M hV hM
  have hNM : N = M := hmax N hMN hN
  subst N
  exact hcount