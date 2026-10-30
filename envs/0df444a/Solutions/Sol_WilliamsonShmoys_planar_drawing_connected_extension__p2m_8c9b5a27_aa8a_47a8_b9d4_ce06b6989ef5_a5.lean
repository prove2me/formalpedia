-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension__p2m_8c9b5a27_aa8a_47a8_b9d4_ce06b6989ef5_a5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T08:31:19.840724+00:00
-- url     : https://prove2.me/submissions/08da902d-1e8f-459c-9b4a-a2e1f3f0088d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_eb36caad_992c_4412_9250_64661542f0e2_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_connected__p2m_eb36caad_992c_4412_9250_64661542f0e2_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K' : SimpleGraph V,
      K'.Connected ∧
      HasPlanarDrawingOn K' ∧
      K.edgeSet.ncard ≤ K'.edgeSet.ncard := by
  obtain ⟨K', hSub, hPlanar, hMax, hEdges⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_eb36caad_992c_4412_9250_64661542f0e2_a1 K hK
  have hConnected :=
    WilliamsonShmoys.maximal_planar_graph_connected__p2m_eb36caad_992c_4412_9250_64661542f0e2_a1 K' hPlanar hMax hCard
  exact ⟨K', hConnected, hPlanar, hEdges⟩