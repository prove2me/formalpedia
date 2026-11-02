-- Prove2me | solution 2 for WilliamsonShmoys.drawable_extension_of_disconnected_planar_graph__p2m_60fad162_757e_4f59_b943_b70a80142f4b_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:19:42.624651+00:00
-- url     : https://prove2.me/submissions/ee8301b5-ce4e-4aa3-a49d-53e7ff3423cb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_drawable_extension_by_joining_components__p2m_10785777_128a_4e88_8513_e417451ea141_a2

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V)
    (hdisc : ¬ M.Connected) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧ N ≠ M := by
  obtain ⟨u, v, huv, N, hMN, huvN, hNplanar, hNM⟩ :=
    WilliamsonShmoys.drawable_extension_by_joining_components__p2m_10785777_128a_4e88_8513_e417451ea141_a2
      M hM hcard hdisc
  exact ⟨N, hMN, hNplanar, hNM⟩