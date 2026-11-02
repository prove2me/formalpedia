-- Prove2me | solution 1 for WilliamsonShmoys.planar_extension_maximal_supergraph__p2m_03fd7227_be52_409b_9f5b_92650e994dba_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:22:56.251209+00:00
-- url     : https://prove2.me/submissions/0746871b-e2f5-48ac-ba62-f2a152601851

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_extension_finite__p2m_89fd7ec5_d704_44ae_9887_a6594412388a_a3

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hKdraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    Exists fun H : SimpleGraph V => And (LE.le K H)
      (And (WilliamsonShmoys.HasPlanarDrawingOn H)
        (∀ J : SimpleGraph V, LE.le H J -> WilliamsonShmoys.HasPlanarDrawingOn J -> LE.le J H)) := by
  exact WilliamsonShmoys.exists_maximal_extension_finite__p2m_89fd7ec5_d704_44ae_9887_a6594412388a_a3
    (P := WilliamsonShmoys.HasPlanarDrawingOn) K hKdraw