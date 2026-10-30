-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_77f664a0
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T21:44:15.317112+00:00
-- url     : https://prove2.me/submissions/aa048b57-2e59-4b84-abf4-89b611286d53

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_with_maximal_edge_count

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : HasPlanarDrawingOn G)
    (hmax : ∀ K : SimpleGraph V,
      (∀ u v, G.Adj u v → K.Adj u v) →
      HasPlanarDrawingOn K →
      ∀ u v, K.Adj u v → G.Adj u v) :
    G.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hsub, hKdraw, hKcount⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph_with_maximal_edge_count
      G hCard hDraw
  have hback : ∀ u v, K.Adj u v → G.Adj u v := hmax K hsub hKdraw
  have hAdj : G.Adj = K.Adj := by
    funext u v
    exact propext ⟨hsub u v, hback u v⟩
  have hEq : G = K := SimpleGraph.ext hAdj
  rw [hEq]
  exact hKcount