-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_strict_extension_step__p2m_5f60d79e_7bc9_419f_998e_e61c453c0681_a2
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:43:15.381994+00:00
-- url     : https://prove2.me/submissions/3777b135-f657-4a72-b985-1762e30ba00f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
        (H : SimpleGraph V),
        WilliamsonShmoys.HasPlanarDrawingOn H →
        ¬ H.Connected →
        ∃ K : SimpleGraph V,
          H.edgeSet ⊂ K.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn K) := by
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
  have hDisconnected : ¬ H.Connected := by
    intro hc
    obtain ⟨x⟩ := hc.nonempty
    exact x.elim
  obtain ⟨K, hstrict, hKDraw⟩ := h (V := Empty) H hDraw hDisconnected
  have hK : K = (⊥ : SimpleGraph Empty) := by
    ext u v
    exact u.elim
  have hKH : K = H := by
    simpa [H] using hK
  rw [hKH] at hstrict
  exact hstrict.2 (fun _ hx => hx)