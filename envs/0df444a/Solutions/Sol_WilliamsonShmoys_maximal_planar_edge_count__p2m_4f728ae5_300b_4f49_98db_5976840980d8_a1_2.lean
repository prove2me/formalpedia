-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count__p2m_4f728ae5_300b_4f49_98db_5976840980d8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:14:10.146185+00:00
-- url     : https://prove2.me/submissions/c5784179-d9ec-43b2-ae88-ef7c3fef1ce5

import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_e8a894df

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.maximal_drawable_edge_count_e8a894df K hcard hplanar hmax
