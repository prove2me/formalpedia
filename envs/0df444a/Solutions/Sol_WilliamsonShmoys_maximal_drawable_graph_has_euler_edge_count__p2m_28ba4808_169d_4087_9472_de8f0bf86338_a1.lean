-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_has_euler_edge_count__p2m_28ba4808_169d_4087_9472_de8f0bf86338_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:57:31.773172+00:00
-- url     : https://prove2.me/submissions/6025c53d-2113-4952-98e9-b9fb91c6c15c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_euler_extension__p2m_8d2492c2_a620_4e30_8a73_7621e3b1e96d_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V,
      letI : DecidableRel L.Adj := Classical.decRel L.Adj
      K ≤ L → HasPlanarDrawingOn L → L ≤ K) :
    letI : DecidableRel K.Adj := Classical.decRel K.Adj
    K.edgeFinset.card + 6 = 3 * Fintype.card V := by
  classical
  obtain ⟨L, hKL, hL, hcount⟩ :=
    WilliamsonShmoys.drawable_graph_has_euler_extension__p2m_8d2492c2_a620_4e30_8a73_7621e3b1e96d_a2
      K hV hK
  have hLK : L ≤ K := hMax L hKL hL
  have hEq : L = K := le_antisymm hLK hKL
  subst L
  simpa using hcount