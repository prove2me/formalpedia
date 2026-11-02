-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_augmentation__p2m_b05b2ac9_cf86_42cd_81eb_d15df4254060_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:59:04.855126+00:00
-- url     : https://prove2.me/submissions/fd48f4e2-4dd0-42c8-9f2a-336ba3da1db5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_planar_supergraph_maximality__p2m_934089cc_df1f_4da4_b973_c115b2e35af8_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       letI : DecidableRel K.Adj := Classical.decRel K.Adj
       H.edgeFinset.card ≤ K.edgeFinset.card) := by
  classical
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.finite_planar_supergraph_maximality__p2m_934089cc_df1f_4da4_b973_c115b2e35af8_a1
      H HasPlanarDrawingOn hH
  refine ⟨K, hHK, hK, ?_, ?_⟩
  · intro L hKL hL
    exact hmax L (le_trans hHK hKL) hL
  · exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hHK)