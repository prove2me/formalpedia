-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_edge_lower_bound__p2m_89969936_4231_4118_a55c_9873f67c1fec_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:36:05.962337+00:00
-- url     : https://prove2.me/submissions/8807bf05-6c48-4b59-8fe9-655b4a01bee9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_bound__p2m_09ee00d6_d6e0_4e98_aab0_c4cdc0b16fb7_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K L : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hmax :
      (letI : ∀ G : SimpleGraph V, DecidableRel G.Adj :=
        fun G => Classical.decRel G.Adj
       K.edgeFinset ⊆ L.edgeFinset ∧
       HasPlanarDrawingOn L ∧
       ∀ M : SimpleGraph V,
         L.edgeFinset ⊆ M.edgeFinset →
         HasPlanarDrawingOn M →
         M.edgeFinset = L.edgeFinset)) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    3 * Fintype.card V - 6 ≤ L.edgeFinset.card := by
  letI : ∀ G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
  rcases hmax with ⟨_, hdrawL, hmaxL⟩
  obtain ⟨M, hsub, hdrawM, hbound⟩ :=
    WilliamsonShmoys.planar_supergraph_edge_bound__p2m_09ee00d6_d6e0_4e98_aab0_c4cdc0b16fb7_a1 L hcard hdrawL
  have hedge : M.edgeFinset = L.edgeFinset := hmaxL M hsub hdrawM
  simpa [hedge] using hbound