-- Prove2me | solution 1 for WilliamsonShmoys.exists_strict_planar_extension_of_not_connected__p2m_53c320f3_e91d_4263_a564_4632ae783af5_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:27:53.931138+00:00
-- url     : https://prove2.me/submissions/530f5fcb-6af2-4073-b454-d4eb3d494261
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_disconnected_partition_nonempty__p2m_6eb1d1e9_05be_4cdb_8344_dedf44e2bf5b_a3
import Theorems.Thm_WilliamsonShmoys_planar_partition_extension__p2m_6eb1d1e9_05be_4cdb_8344_dedf44e2bf5b_a3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M)
    (hdisc : ¬ M.Connected) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧ ¬ N ≤ M := by
  obtain ⟨A, hA, hAc, hcross⟩ :=
    WilliamsonShmoys.exists_disconnected_partition_nonempty__p2m_6eb1d1e9_05be_4cdb_8344_dedf44e2bf5b_a3
      M hcard hdisc
  exact WilliamsonShmoys.planar_partition_extension__p2m_6eb1d1e9_05be_4cdb_8344_dedf44e2bf5b_a3
    M A hA hAc hcross hM