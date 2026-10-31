-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_6cc89dc0_dca8_4f92_990f_6ab07c5977c9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:46:15.646963+00:00
-- url     : https://prove2.me/submissions/ae511f5f-4022-4dcd-9c48-3b91d0d90127

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_subgraph__p2m_8c20c3de_e0e6_4d41_88fb_de4af60b0786_a1
import Theorems.Thm_finite_maximal_extension_for_downward_closed_graph_property__p2m_8c20c3de_e0e6_4d41_88fb_de4af60b0786_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) :
    Exists fun T : SimpleGraph V =>
      And (LE.le H T) (And (HasPlanarDrawingOn T)
      (forall T' : SimpleGraph V, LE.le T T' -> HasPlanarDrawingOn T' -> T' = T)) := by
  let P : SimpleGraph V → Prop := HasPlanarDrawingOn
  have hdown : ∀ {G K : SimpleGraph V}, G ≤ K → P K → P G := by
    intro G K hGK hK
    exact WilliamsonShmoys.planarDrawingOn_subgraph__p2m_8c20c3de_e0e6_4d41_88fb_de4af60b0786_a1 hGK hK
  obtain ⟨T, hHT, hPT, hmax⟩ :=
    finite_maximal_extension_for_downward_closed_graph_property__p2m_8c20c3de_e0e6_4d41_88fb_de4af60b0786_a1
      P hdown H hH
  exact ⟨T, hHT, hPT, fun T' hTT' hPT' => hmax T' hTT' hPT'⟩