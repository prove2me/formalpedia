-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_connected__p2m_4231ee8f_e4d1_40b7_a8b0_f5da488ab36d_a4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:48:55.819529+00:00
-- url     : https://prove2.me/submissions/d26a13a3-53c2-42ed-ba29-aac7067ab0f1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic
import Theorems.Thm_WilliamsonShmoys_disconnected_planar_graph_has_strict_planar_supergraph__p2m_a8cc1130_463b_4047_8c5c_3f482bfddd2a_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ M : SimpleGraph V, H ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = H) :
    H.Connected := by
  by_contra hNotConnected
  obtain ⟨M, hHM, hMPlanar, hMNe⟩ :=
    WilliamsonShmoys.disconnected_planar_graph_has_strict_planar_supergraph__p2m_a8cc1130_463b_4047_8c5c_3f482bfddd2a_a1
      H hH hV hNotConnected
  have hEq : M = H := hMax M hHM hMPlanar
  exact hMNe hEq