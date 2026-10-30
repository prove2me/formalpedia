-- Prove2me | solution 1 for WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_2094dec4_72bc_4506_8cb1_28494e96e3ad_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:40:22.461397+00:00
-- url     : https://prove2.me/submissions/7536f004-bae7-4ae9-9083-9cb2fd10c0c7

import Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exact_edge_count
import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hconn : K.Connected)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  obtain ⟨L, hKL, hL, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count K hV hK
  have hLK : L = K := hmax L hKL hL
  rw [hLK] at hcount
  omega