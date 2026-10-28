-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_simpleGraph_family
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:22:27.718616+00:00
-- url     : https://prove2.me/submissions/68c55e1f-65ff-4232-a45a-3854f8944266

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (hP : ∃ G : SimpleGraph V, P G) :
    ∃ G : SimpleGraph V, P G ∧
      ∀ L : SimpleGraph V, P L → G ≤ L → L = G := by
  classical
  obtain ⟨G, hG⟩ := (SimpleGraph.exists_isExtremal_iff_exists P).2 hP
  rcases hG with ⟨dG, hG⟩
  letI : DecidableRel G.Adj := dG
  refine ⟨G, hG.1, ?_⟩
  intro L hL hGL
  have hEq : G = L := (SimpleGraph.IsExtremal.le_iff_eq hG hL).1 hGL
  exact hEq.symm