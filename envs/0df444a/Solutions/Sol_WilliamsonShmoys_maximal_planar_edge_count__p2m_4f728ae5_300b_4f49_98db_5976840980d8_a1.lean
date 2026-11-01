-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_4f728ae5_300b_4f49_98db_5976840980d8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:40:46.451205+00:00
-- url     : https://prove2.me/submissions/b031a9ca-af17-49ab-9aee-54c11e75c222

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_26140903_fcb8_4c7c_a0cc_72edca446c76_a1
open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hLplanar, hLcount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_26140903_fcb8_4c7c_a0cc_72edca446c76_a1
      K hplanar hcard
  have hLK : L = K := hmax L hKL hLplanar
  simpa [hLK] using hLcount