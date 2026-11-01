-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_maximal__p2m_4f728ae5_300b_4f49_98db_5976840980d8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:40:51.070919+00:00
-- url     : https://prove2.me/submissions/aded6060-dffe-49be-a6cb-358b8f7b6d27

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_maximal_simpleGraph_extension__p2m_eb256fa3_9e89_4cdb_b978_02905f819491_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ HasPlanarDrawingOn K ∧
        ∀ L : SimpleGraph V,
          K ≤ L → HasPlanarDrawingOn L → L = K := by
  exact finite_maximal_simpleGraph_extension__p2m_eb256fa3_9e89_4cdb_b978_02905f819491_a1
    H HasPlanarDrawingOn hplanar