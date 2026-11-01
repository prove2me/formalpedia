-- Prove2me | solution 2 for WilliamsonShmoys.planar_connected_supergraph__p2m_81eecf30_e96c_499d_b4eb_13964c396f7c_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:17:22.367728+00:00
-- url     : https://prove2.me/submissions/b6bf4f37-3c75-48a7-96ca-6beb2c26721e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_nonconnected_edge_attachment__p2m_7d9aa82d_f2fe_4aa2_b79e_d2d48fb9feb3_a5
import Theorems.Thm_WilliamsonShmoys_planar_augmentation_iteration__p2m_7d9aa82d_f2fe_4aa2_b79e_d2d48fb9feb3_a5

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    ∃ C : SimpleGraph V,
      G ≤ C ∧ C.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn C := by
  exact WilliamsonShmoys.planar_augmentation_iteration__p2m_7d9aa82d_f2fe_4aa2_b79e_d2d48fb9feb3_a5
    G hG hcard (by
      intro H hGH hH hdis
      exact WilliamsonShmoys.planar_nonconnected_edge_attachment__p2m_7d9aa82d_f2fe_4aa2_b79e_d2d48fb9feb3_a5
        H hH hcard hdis)