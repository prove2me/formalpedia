-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_c77f60cb_52bf_4945_9bde_3c0cc2df12db_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T11:00:17.026758+00:00
-- url     : https://prove2.me/submissions/9c2e43f9-e4de-4c30-a84f-960a2374be0a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_cf998a55_167a_4517_9269_e98de5b379a5_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hKdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hKmax : ∀ L : SimpleGraph V,
      (∀ u v, K.Adj u v → L.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      (∀ u v, L.Adj u v → K.Adj u v))
    (hV : 3 ≤ Fintype.card V) : K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨T, hKT, hTdraw, hTcount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_cf998a55_167a_4517_9269_e98de5b379a5_a1
      K hKdraw hV
  have hTK : ∀ u v, T.Adj u v → K.Adj u v := hKmax T hKT hTdraw
  have hEq : K = T := by
    ext u v
    exact ⟨hKT u v, hTK u v⟩
  have hCount : K.edgeSet.ncard = T.edgeSet.ncard := by
    simpa only [hEq]
  rw [hCount]
  exact hTcount