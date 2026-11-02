-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_connected__p2m_801cf2e4_6b6e_4272_a43f_109c3b8f7482_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:13:07.500206+00:00
-- url     : https://prove2.me/submissions/684e0e40-6aa5-442b-b505-3584358445cf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_disconnected_planar_graph_has_planar_strict_extension__p2m_a0a9770d_b636_48de_8b32_1b32b62691e8_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      (∀ u v, K.Adj u v → L.Adj u v) →
      HasPlanarDrawingOn L →
      ∀ u v, L.Adj u v → K.Adj u v) :
    K.Connected := by
  by_contra hconn
  obtain ⟨L, hKL, hL, u, v, huv, hnot⟩ :=
    WilliamsonShmoys.disconnected_planar_graph_has_planar_strict_extension__p2m_a0a9770d_b636_48de_8b32_1b32b62691e8_a1
      K hK hconn
  exact hnot (hmax L hKL hL u v huv)