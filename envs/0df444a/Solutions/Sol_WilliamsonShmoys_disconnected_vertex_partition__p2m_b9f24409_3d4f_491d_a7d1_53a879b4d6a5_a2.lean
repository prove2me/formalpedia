-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_vertex_partition__p2m_b9f24409_3d4f_491d_a7d1_53a879b4d6a5_a2
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:22:18.741642+00:00
-- url     : https://prove2.me/submissions/dd4e446b-8fb8-41b8-a8dc-22638475a2ce

import Mathlib

set_option autoImplicit false

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
        (M : SimpleGraph V) (hDisc : ¬ M.Connected),
        ∃ A : Set V, A.Nonempty ∧ Aᶜ.Nonempty ∧
          (∀ ⦃u v : V⦄, u ∈ A → v ∉ A → ¬ M.Adj u v)) := by
  intro h
  let M : SimpleGraph Empty := ⊥
  have hDisc : ¬ M.Connected := by
    intro hc
    exact hc.nonempty.elim (fun x => nomatch x)
  obtain ⟨A, hA, _, _⟩ := h M hDisc
  rcases hA with ⟨x, _⟩
  exact nomatch x