-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_6b40c087_f0a0_4e97_a1ee_42212d56c9dd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:44:47.207696+00:00
-- url     : https://prove2.me/submissions/ee4c20c4-0e98-47d2-b725-92b69172b84d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exact_edge_count
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) :
    3 * Fintype.card V = K.edgeSet.ncard + 6 := by
  obtain ⟨N, hKN, hN, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count K hV hK
  have hNK : N = K := hmax N hKN hN
  subst N
  omega