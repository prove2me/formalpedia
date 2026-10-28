-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_planar_drawing_has_proper_drawable_supergraph
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T01:57:11.035113+00:00
-- url     : https://prove2.me/submissions/9b265f1d-a38b-4505-84e0-dca77b06f586
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_nonreachable_pair
import Theorems.Thm_WilliamsonShmoys_add_edge_between_nonreachable_vertices

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hdisc : ¬ H.Connected) :
    ∃ L : SimpleGraph V, H ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ ¬ L ≤ H := by
  obtain ⟨u, v, huv, hnotAdj, hnotReach⟩ :=
    WilliamsonShmoys.exists_nonreachable_pair H hV hdisc
  obtain ⟨L, hHL, hdraw, huvL⟩ :=
    WilliamsonShmoys.add_edge_between_nonreachable_vertices H hH hnotReach
  refine ⟨L, hHL, hdraw, ?_⟩
  intro hLH
  exact hnotAdj (hLH huvL)