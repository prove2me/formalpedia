-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_8b510604_ecbe_41a0_8ffc_c43a355d8485_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:04:16.59479+00:00
-- url     : https://prove2.me/submissions/96c1d1f2-2dd9-4ad8-9e22-0f89ac4cdf0a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulating_extension__p2m_dafc8434_c658_484f_b8e8_b76293ec5b82_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hconn : H.Connected)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel H.Adj := Classical.decRel _
    (∀ K : SimpleGraph V,
      (letI : DecidableRel K.Adj := Classical.decRel _;
       H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H)) →
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  classical
  letI : DecidableRel H.Adj := Classical.decRel _
  intro hmax
  obtain ⟨K, hHK, hKplanar, hKcount⟩ :=
    WilliamsonShmoys.planar_graph_has_triangulating_extension__p2m_dafc8434_c658_484f_b8e8_b76293ec5b82_a1
      H hplanar hcard
  have hKH : K = H := hmax K hHK hKplanar
  simpa [hKH] using hKcount