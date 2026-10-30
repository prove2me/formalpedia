-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_connected_extension__p2m_425c8e2e_b612_4bb5_a030_cd4c3c162389_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:50:28.570242+00:00
-- url     : https://prove2.me/submissions/800a3a57-df68-4e0f-8863-f140ca6f0fa9

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
        (H : SimpleGraph V),
        WilliamsonShmoys.HasPlanarDrawingOn H →
        ∃ K : SimpleGraph V,
          H.edgeSet ⊆ K.edgeSet ∧ K.Connected ∧
            WilliamsonShmoys.HasPlanarDrawingOn K) := by
  intro h
  let H : SimpleGraph Empty := ⊥
  have hDraw : WilliamsonShmoys.HasPlanarDrawingOn H := by
    refine ⟨(fun x : Empty => x.elim), (fun x y t => x.elim), ?_⟩
    constructor
    · intro x y hxy
      exact x.elim
    constructor
    · intro u v huv hadj
      exact u.elim
    · intro u v x y huv hxy hadj hadj' hne t ht s hs heq
      exact u.elim
  obtain ⟨K, hSub, hConn, hKDraw⟩ := h (V := Empty) H hDraw
  obtain ⟨x⟩ := hConn.nonempty
  exact x.elim