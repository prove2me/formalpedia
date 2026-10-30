-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_abdda8c5_f5c1_4e5d_b801_c7084d469782_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:50:14.681846+00:00
-- url     : https://prove2.me/submissions/521a4568-e9a6-4d11-bacb-9399d034fd7c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_triangulated_planar_extension__p2m_7b40ef00_72b0_4fde_a3cb_cf2325177ae8_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  obtain ⟨K, hHK, hK, hcount⟩ :=
    WilliamsonShmoys.exists_triangulated_planar_extension__p2m_7b40ef00_72b0_4fde_a3cb_cf2325177ae8_a1
      H hH hV
  have hKH : K ≤ H := hmax K hHK hK
  have hEq : K = H := le_antisymm hKH hHK
  simpa [hEq] using hcount.le