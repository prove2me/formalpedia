-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_bound__p2m_826e5589_6c55_45ce_83c1_aa1fee8116e2_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:34:21.925593+00:00
-- url     : https://prove2.me/submissions/220806b7-df78-4a3d-9f4d-787e65a1200f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_exact_edge_count_completion__p2m_4389f167_4c7c_4d6b_b9d1_6f89e764ff11_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, G ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = G) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨K, hGK, hK, hedge⟩ :=
    WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_4389f167_4c7c_4d6b_b9d1_6f89e764ff11_a1
      G hG hV
  have hKG : K = G := hmax K hGK hK
  have hedge' : G.edgeSet.ncard + 6 = 3 * Fintype.card V := by
    simpa [hKG] using hedge
  exact le_of_eq hedge'