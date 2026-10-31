-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_303ddd52_95e9_4125_a752_478be76ea7a5_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:40:52.825517+00:00
-- url     : https://prove2.me/submissions/93d97965-e2f8-4ff8-a19f-710bace18aaf

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_lower__p2m_0b1d558b_5b99_484a_a69e_3ba1af67a959_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper__p2m_0b1d558b_5b99_484a_a69e_3ba1af67a959_a1
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hconn : T.Connected)
    (hT : HasPlanarDrawingOn T)
    (hmax : ∀ S : SimpleGraph V, T ≤ S → HasPlanarDrawingOn S → S = T) :
    T.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hlow := WilliamsonShmoys.maximal_drawable_edge_lower__p2m_0b1d558b_5b99_484a_a69e_3ba1af67a959_a1
    T hV hconn hT hmax
  have hupp := WilliamsonShmoys.planar_edge_upper__p2m_0b1d558b_5b99_484a_a69e_3ba1af67a959_a1
    T hV hT
  omega