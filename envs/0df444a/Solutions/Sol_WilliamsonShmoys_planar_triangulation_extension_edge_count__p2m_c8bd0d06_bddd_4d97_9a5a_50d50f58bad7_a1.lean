-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension_edge_count__p2m_c8bd0d06_bddd_4d97_9a5a_50d50f58bad7_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:42:21.489015+00:00
-- url     : https://prove2.me/submissions/ecbc6a91-82cf-49a8-a386-fff66b4b5e25
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connected_extension__p2m_6d61c34e_acf2_4651_8c9f_45d89df1db8f_a1
import Theorems.Thm_WilliamsonShmoys_connected_planar_triangulation__p2m_6d61c34e_acf2_4651_8c9f_45d89df1db8f_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hLK, hKplanar, hKconn⟩ :=
    WilliamsonShmoys.planar_connected_extension__p2m_6d61c34e_acf2_4651_8c9f_45d89df1db8f_a1
      L hplanar (by omega)
  obtain ⟨M, hKM, hMplanar, hMcount⟩ :=
    WilliamsonShmoys.connected_planar_triangulation__p2m_6d61c34e_acf2_4651_8c9f_45d89df1db8f_a1
      K hKplanar hKconn hV
  exact ⟨M, hLK.trans hKM, hMplanar, hMcount⟩