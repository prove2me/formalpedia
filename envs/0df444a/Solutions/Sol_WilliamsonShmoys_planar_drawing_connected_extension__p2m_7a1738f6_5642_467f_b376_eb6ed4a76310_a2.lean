-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension__p2m_7a1738f6_5642_467f_b376_eb6ed4a76310_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T01:05:07.031881+00:00
-- url     : https://prove2.me/submissions/e4ed52e3-f4c8-4ada-a05f-079c82e8df8b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_84aa0f8d_42a4_4615_a166_b73b4ced676a_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_maximal_connected__p2m_84aa0f8d_42a4_4615_a166_b73b4ced676a_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by
  obtain ⟨H, hKH, hH, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_84aa0f8d_42a4_4615_a166_b73b4ced676a_a1
      K hV hK
  exact ⟨H, hKH,
    WilliamsonShmoys.planar_edge_maximal_connected__p2m_84aa0f8d_42a4_4615_a166_b73b4ced676a_a1
      H hV hH hmax,
    hH⟩
