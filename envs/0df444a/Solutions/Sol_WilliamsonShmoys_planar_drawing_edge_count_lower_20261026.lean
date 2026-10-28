-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_lower_20261026
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T12:08:24.336351+00:00
-- url     : https://prove2.me/submissions/95844fb1-33b8-4345-b288-39b982bb519c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_extension

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hV : 3 ≤ Fintype.card V)
    (hPmax : ∀ Q : SimpleGraph V,
      P.edgeSet ⊂ Q.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn Q) :
    3 * Fintype.card V - 6 ≤ P.edgeSet.ncard := by
  by_contra h
  have hlt : P.edgeSet.ncard < 3 * Fintype.card V - 6 := by omega
  obtain ⟨Q, hsub, hQ⟩ :=
    WilliamsonShmoys.planar_drawing_edge_count_extension P hP hV hlt
  exact (hPmax Q hsub) hQ