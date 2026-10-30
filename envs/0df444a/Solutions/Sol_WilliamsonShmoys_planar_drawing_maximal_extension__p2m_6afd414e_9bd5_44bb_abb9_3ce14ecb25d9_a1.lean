-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_6afd414e_9bd5_44bb_abb9_3ce14ecb25d9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:21:08.412262+00:00
-- url     : https://prove2.me/submissions/f501ac43-bdb6-442d-9f4a-a393baa4e49b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_for_finite_property__p2m_d861cb11_4d1d_4208_9ad9_8ec6eefefc53_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, ∃ (_ : DecidableRel H.Adj),
      G.edgeFinset ⊆ H.edgeFinset ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by
  classical
  obtain ⟨H, dH, hGH, hH, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_supergraph_for_finite_property__p2m_d861cb11_4d1d_4208_9ad9_8ec6eefefc53_a1
      (V := V) G WilliamsonShmoys.HasPlanarDrawingOn hG
  exact ⟨H, dH, hGH, hH, fun K hrel hK => hmax K hrel hK⟩