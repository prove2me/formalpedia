-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_7c073d05_f8af_49af_8234_528c2585cbfc_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:05:23.859706+00:00
-- url     : https://prove2.me/submissions/9c55ae57-4aa6-471d-8516-701e239afd43
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_8a1d6513_cc2f_4bb4_9ed2_73bf53ea1ce0_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_triangulation_edge_count__p2m_8a1d6513_cc2f_4bb4_9ed2_73bf53ea1ce0_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hconn : H.Connected)
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
    ∃ K : SimpleGraph V,
      H.edgeFinset ⊆ K.edgeFinset ∧
      HasPlanarDrawingOn K ∧
      K.edgeFinset.card + 6 = 3 * Fintype.card V := by
  classical
  obtain ⟨K, hHK, hK, hKconn, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_8a1d6513_cc2f_4bb4_9ed2_73bf53ea1ce0_a1
      H hconn hH
  refine ⟨K, hHK, hK, ?_⟩
  exact WilliamsonShmoys.maximal_planar_drawing_has_triangulation_edge_count__p2m_8a1d6513_cc2f_4bb4_9ed2_73bf53ea1ce0_a1
    K hKconn hK hcard hmax