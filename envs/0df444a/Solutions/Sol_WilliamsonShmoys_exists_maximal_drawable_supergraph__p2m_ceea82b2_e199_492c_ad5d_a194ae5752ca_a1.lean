-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_ceea82b2_e199_492c_ad5d_a194ae5752ca_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:53:27.347135+00:00
-- url     : https://prove2.me/submissions/c65d665f-6a83-4271-95e5-fdd47dc57ce3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_hasPlanarDrawingOn_mono__p2m_dde6c772_1281_4d21_9b54_46ae763d0262_a1
import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_of_hereditary__p2m_dde6c772_1281_4d21_9b54_46ae763d0262_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    Exists fun W : SimpleGraph V => And (LE.le G W)
      (And (WilliamsonShmoys.HasPlanarDrawingOn W)
        (forall X : SimpleGraph V, LE.le W X -> WilliamsonShmoys.HasPlanarDrawingOn X -> X = W)) := by
  exact WilliamsonShmoys.exists_maximal_supergraph_of_hereditary__p2m_dde6c772_1281_4d21_9b54_46ae763d0262_a1
    (P := WilliamsonShmoys.HasPlanarDrawingOn)
    (hmono := fun {A B} hAB hB =>
      WilliamsonShmoys.hasPlanarDrawingOn_mono__p2m_dde6c772_1281_4d21_9b54_46ae763d0262_a1 hAB hB)
    G hG