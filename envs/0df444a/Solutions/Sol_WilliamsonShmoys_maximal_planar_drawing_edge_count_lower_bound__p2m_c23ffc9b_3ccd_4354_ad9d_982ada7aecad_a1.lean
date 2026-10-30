-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_c23ffc9b_3ccd_4354_ad9d_982ada7aecad_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:21:06.074913+00:00
-- url     : https://prove2.me/submissions/21ca6297-dcc4-4c2c-b071-be6b063c4ed8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_edge_extension_count__p2m_3d35c422_26b2_44b6_842a_87c2ee457863_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) (hMax : ∀ L : SimpleGraph V, H ≤ L → HasPlanarDrawingOn L → L = H) : 3 * Fintype.card V - 6 ≤ H.edgeSet.ncard := by
  obtain ⟨L, hHL, hL, hcount⟩ := WilliamsonShmoys.planar_drawing_has_maximal_edge_extension_count__p2m_3d35c422_26b2_44b6_842a_87c2ee457863_a1 H hH hV
  have hEq : L = H := hMax L hHL hL
  subst L
  omega