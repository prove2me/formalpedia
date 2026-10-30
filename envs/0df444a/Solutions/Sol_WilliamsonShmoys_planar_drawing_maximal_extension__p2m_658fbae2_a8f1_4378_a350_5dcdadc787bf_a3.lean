-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_658fbae2_a8f1_4378_a350_5dcdadc787bf_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:29:50.1934+00:00
-- url     : https://prove2.me/submissions/dab28912-aadc-4c07-8e99-9bc81b31e326

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_of_finite_property__p2m_e2b131f7_3fa6_4028_b77b_f247189916b8_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      G ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M := by
  refine WilliamsonShmoys.exists_maximal_supergraph_of_finite_property__p2m_e2b131f7_3fa6_4028_b77b_f247189916b8_a1
    (P := WilliamsonShmoys.HasPlanarDrawingOn) (G := G) ?_ hG
  intro A B hAB hB
  rcases hB with ⟨p, arc, hp, hedge, hcross⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hAdj
    exact hedge u v huv (hAB hAdj)
  · intro u v x y huv hxy hAdj hAdj' hne t ht s hs hint
    exact hcross u v x y huv hxy (hAB hAdj) (hAB hAdj') hne t ht s hs hint