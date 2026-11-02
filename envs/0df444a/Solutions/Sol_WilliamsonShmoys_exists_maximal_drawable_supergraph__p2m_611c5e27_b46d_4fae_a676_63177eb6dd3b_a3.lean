-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_611c5e27_b46d_4fae_a676_63177eb6dd3b_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:01:20.156622+00:00
-- url     : https://prove2.me/submissions/26fc7fa0-d08f-4bba-bc39-0e5671f9a5cf

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_exists_maximal_supergraph_of_downward_closed__p2m_5641e734_866b_4e6a_9d69_40c2e1f45d44_a1
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V, G ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ H : SimpleGraph V, K ≤ H → HasPlanarDrawingOn H → H ≤ K := by
  classical
  have hdown : ∀ {A B : SimpleGraph V}, A ≤ B →
      HasPlanarDrawingOn B → HasPlanarDrawingOn A := by
    intro A B hAB hB
    rcases hB with ⟨p, arc, hp, hedge, hcross⟩
    refine ⟨p, arc, hp, ?_, ?_⟩
    · intro u v huv hadj
      exact hedge u v huv (hAB hadj)
    · intro u v x y huv hxy hadjA hadjA' hne t ht s hs heq
      exact hcross u v x y huv hxy (hAB hadjA) (hAB hadjA') hne t ht s hs heq
  exact exists_maximal_supergraph_of_downward_closed__p2m_5641e734_866b_4e6a_9d69_40c2e1f45d44_a1
    HasPlanarDrawingOn hdown G hG
