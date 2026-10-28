-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound__p2m_ca3bbeaf_b99d_433d_8549_4f9fe71c79f9_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:00:58.102775+00:00
-- url     : https://prove2.me/submissions/8507e415-3cdd-4b4a-88f3-351521174668
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_f09f3524_c856_4011_8ae0_deaee3a01b51_a1
import Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono__p2m_f09f3524_c856_4011_8ae0_deaee3a01b51_a1

set_option autoImplicit false

open SimpleGraph

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hV : 3 <= Fintype.card V) :
    N.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨M, hNM, hMplanar, hMcount⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_f09f3524_c856_4011_8ae0_deaee3a01b51_a1 N hN hV
  have hle := WilliamsonShmoys.edgeSet_ncard_mono__p2m_f09f3524_c856_4011_8ae0_deaee3a01b51_a1 N M hNM
  omega