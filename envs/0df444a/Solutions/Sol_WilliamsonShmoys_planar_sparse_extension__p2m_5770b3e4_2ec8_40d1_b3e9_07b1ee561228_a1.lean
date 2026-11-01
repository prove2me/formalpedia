-- Prove2me | solution 1 for WilliamsonShmoys.planar_sparse_extension__p2m_5770b3e4_2ec8_40d1_b3e9_07b1ee561228_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:16:40.863459+00:00
-- url     : https://prove2.me/submissions/bba6f12b-7f45-477b-b841-fd4e03f9a4a4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_sparse_extension_maximal_drawable_supergraph__p2m_8878012f_4621_4e20_8c97_e8aa106c5519_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_bound__p2m_8878012f_4621_4e20_8c97_e8aa106c5519_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {U : Type} [Fintype U] [LinearOrder U]
    (K : SimpleGraph U) (hcard : 3 ≤ Fintype.card U)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hsparse : K.edgeSet.ncard < 3 * Fintype.card U - 6) :
    ∃ L : SimpleGraph U, K ≤ L ∧ K ≠ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L := by
  classical
  obtain ⟨L, hKL, hLdraw, hLmax⟩ :=
    WilliamsonShmoys.planar_sparse_extension_maximal_drawable_supergraph__p2m_8878012f_4621_4e20_8c97_e8aa106c5519_a1 K hdraw
  by_cases hneq : K = L
  · subst L
    have hbound :=
      WilliamsonShmoys.maximal_planar_graph_edge_bound__p2m_8878012f_4621_4e20_8c97_e8aa106c5519_a1 K hcard hdraw hLmax
    exact False.elim ((Nat.not_lt_of_ge hbound) hsparse)
  · exact ⟨L, hKL, hneq, hLdraw⟩