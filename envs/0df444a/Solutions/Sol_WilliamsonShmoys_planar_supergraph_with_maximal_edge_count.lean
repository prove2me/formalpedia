-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_with_maximal_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T03:46:25.267529+00:00
-- url     : https://prove2.me/submissions/4f7c600a-856e-4c4f-870f-6ac3b7b6caee

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_extension_a9181169_d523_4da1_8834_b734217e5ad6
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_a9181169_d523_4da1_8834_b734217e5ad6

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ T : SimpleGraph V, HasPlanarDrawingOn T ∧
      (∀ u v, G.Adj u v → T.Adj u v) ∧
      T.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨T, hT, hGT, hmax⟩ :=
    WilliamsonShmoys.planar_supergraph_extension_a9181169_d523_4da1_8834_b734217e5ad6 G hG
  exact ⟨T, hT, hGT,
    WilliamsonShmoys.maximal_planar_edge_count_a9181169_d523_4da1_8834_b734217e5ad6 T hT hCard hmax⟩