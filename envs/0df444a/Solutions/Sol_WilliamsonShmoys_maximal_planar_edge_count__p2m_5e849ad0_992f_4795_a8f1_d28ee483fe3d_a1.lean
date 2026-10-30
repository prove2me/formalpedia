-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_5e849ad0_992f_4795_a8f1_d28ee483fe3d_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:55:17.849509+00:00
-- url     : https://prove2.me/submissions/890a87dd-ccbf-4a09-9dd0-317f98e51fc2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_1cedfa43_e759_4304_8f59_175ee0ad0ade_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_1cedfa43_e759_4304_8f59_175ee0ad0ade_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hUpper :=
    WilliamsonShmoys.planar_edge_upper_bound__p2m_1cedfa43_e759_4304_8f59_175ee0ad0ade_a1
      L hDraw hV
  have hLower :=
    WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_1cedfa43_e759_4304_8f59_175ee0ad0ade_a1
      L hDraw hV hMax
  exact Nat.le_antisymm hUpper hLower