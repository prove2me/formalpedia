-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_disconnected_extension__p2m_29b7bd89_c713_464d_96d1_5b54a307b779_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:28:06.566089+00:00
-- url     : https://prove2.me/submissions/ff3cc376-3e57-4fc7-bb11-f5bd4f82fbbb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_has_unreachable_pair__p2m_834fbbd6_f11e_4933_84c3_a729cabab29e_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_bridge_between_unreachable_vertices__p2m_834fbbd6_f11e_4933_84c3_a729cabab29e_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ¬ H.Connected →
      ∃ u v, ¬ H.Reachable u v ∧
        HasPlanarDrawingOn
          (H ⊔ SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 V))) := by
  intro hdis
  obtain ⟨u, v, hnot⟩ :=
    WilliamsonShmoys.disconnected_has_unreachable_pair__p2m_834fbbd6_f11e_4933_84c3_a729cabab29e_a1
      H hcard hdis
  exact ⟨u, v, hnot,
    WilliamsonShmoys.planar_drawing_add_bridge_between_unreachable_vertices__p2m_834fbbd6_f11e_4933_84c3_a729cabab29e_a1
      H hH u v hnot⟩
