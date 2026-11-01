-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_49e59269_0942_49a7_bb42_8d7dcf799486_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:01:01.866748+00:00
-- url     : https://prove2.me/submissions/b5429a13-95ab-4657-acad-ce55930b68a3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_5770b3e4_2ec8_40d1_b3e9_07b1ee561228_a1
import Theorems.Thm_WilliamsonShmoys_planar_sparse_extension__p2m_5770b3e4_2ec8_40d1_b3e9_07b1ee561228_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {U : Type} [Fintype U] [LinearOrder U]
    (K : SimpleGraph U) (hcard : 3 ≤ Fintype.card U)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph U, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → K = L) :
    3 * Fintype.card U - 6 = K.edgeSet.ncard := by
  have hupper := WilliamsonShmoys.planar_edge_count_upper_bound__p2m_5770b3e4_2ec8_40d1_b3e9_07b1ee561228_a1 K hcard hdraw
  by_contra htarget
  have hsparse : K.edgeSet.ncard < 3 * Fintype.card U - 6 := by omega
  obtain ⟨L, hKL, hneq, hLdraw⟩ :=
    WilliamsonShmoys.planar_sparse_extension__p2m_5770b3e4_2ec8_40d1_b3e9_07b1ee561228_a1 K hcard hdraw hsparse
  exact hneq (hmax L hKL hLdraw)