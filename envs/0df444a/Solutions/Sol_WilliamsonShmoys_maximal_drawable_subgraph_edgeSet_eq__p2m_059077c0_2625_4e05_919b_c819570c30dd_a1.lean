-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_subgraph_edgeSet_eq__p2m_059077c0_2625_4e05_919b_c819570c30dd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:47:38.885111+00:00
-- url     : https://prove2.me/submissions/fbb77047-3644-4240-bc43-dce76390519b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (S T : SimpleGraph V)
    (hST : ∀ u v, S.Adj u v → T.Adj u v)
    (hT : HasPlanarDrawingOn T)
    (hMax : ∀ U : SimpleGraph V,
      (∀ u v, S.Adj u v → U.Adj u v) →
      HasPlanarDrawingOn U →
      ∀ u v, U.Adj u v → S.Adj u v) :
    S.edgeSet.ncard = T.edgeSet.ncard := by
  have hTS : ∀ u v, T.Adj u v → S.Adj u v := hMax T hST hT
  have hEq : S = T := by
    ext u v
    exact ⟨hST u v, hTS u v⟩
  exact congrArg (fun G : SimpleGraph V => G.edgeSet.ncard) hEq