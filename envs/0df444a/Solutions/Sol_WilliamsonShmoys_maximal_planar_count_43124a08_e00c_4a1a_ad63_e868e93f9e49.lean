-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_count_43124a08_e00c_4a1a_ad63_e868e93f9e49
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T00:52:49.247821+00:00
-- url     : https://prove2.me/submissions/19a35bb2-7c81-4731-bb13-fb71b7044254
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_3fe6515b_8335_4a72_a208_f1a2ec6f6eaf
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_3fe6515b_8335_4a72_a208_f1a2ec6f6eaf
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hmax : WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ J : SimpleGraph V, H.edgeSet ⊆ J.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn J → J.edgeSet = H.edgeSet) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper := WilliamsonShmoys.planar_edge_count_upper_bound_3fe6515b_8335_4a72_a208_f1a2ec6f6eaf H hmax.1 hV
  have hlower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound_3fe6515b_8335_4a72_a208_f1a2ec6f6eaf H hmax hV
  omega