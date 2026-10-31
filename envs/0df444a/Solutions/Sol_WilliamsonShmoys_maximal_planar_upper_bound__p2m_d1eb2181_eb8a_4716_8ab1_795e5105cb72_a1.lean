-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_upper_bound__p2m_d1eb2181_eb8a_4716_8ab1_795e5105cb72_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:04:07.218282+00:00
-- url     : https://prove2.me/submissions/9900fe0b-690d-4767-810e-2f22e5e0b8f4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_2e520467_0d96_4c71_b340_b60069871ecd_a1
import Theorems.Thm_WilliamsonShmoys_planar_connected_edge_bound__p2m_2e520467_0d96_4c71_b340_b60069871ecd_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H) (hV : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨K, hHK, hcard, hKconn, hKplanar⟩ :=
    WilliamsonShmoys.planar_drawing_connected_extension__p2m_2e520467_0d96_4c71_b340_b60069871ecd_a1
      H hH
  have hbound :=
    WilliamsonShmoys.planar_connected_edge_bound__p2m_2e520467_0d96_4c71_b340_b60069871ecd_a1
      K hKplanar hKconn hV
  omega