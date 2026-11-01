-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_b4696467_bd7a_4833_91a4_199ab5144504_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:29:03.425546+00:00
-- url     : https://prove2.me/submissions/5edac492-cb93-44d4-8718-3cbe3ab19fac

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_triangulation_extension__p2m_77d68189_39bf_4e13_b3a3_9f804ba94476_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L → K ≤ L → K = L)
    (hcard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  obtain ⟨L, hL, hKL, hcount⟩ :=
    WilliamsonShmoys.maximal_planar_triangulation_extension__p2m_77d68189_39bf_4e13_b3a3_9f804ba94476_a1
      K hplanar hcard
  have hEq : K = L := hmax L hL hKL
  have hEdges : L.edgeSet.ncard = K.edgeSet.ncard := by
    rw [hEq]
  omega