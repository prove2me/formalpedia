-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_bound__p2m_46fe5fa5_fbe5_4667_8617_73807c0b1344_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:18:27.637902+00:00
-- url     : https://prove2.me/submissions/b3e7152c-42ba-43e6-93e8-9374a2cefc57

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_fed4729c_77e3_4492_a45e_1ab93cbddb9e_a1

set_option autoImplicit false

open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K)
    (hV : 3 <= Fintype.card V) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨L, hKL, hLplanar, hLedges⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_fed4729c_77e3_4492_a45e_1ab93cbddb9e_a1
      K hplanar hV
  have hLK : L = K := hmax L hKL hLplanar
  rw [← hLK]
  exact hLedges.le