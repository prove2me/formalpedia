-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_extension_of_downward_closed__p2m_b230c174_4dc5_4f1c_a300_93827e81df10_a1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:19:15.169703+00:00
-- url     : https://prove2.me/submissions/19824bdb-a519-4cf6-831e-119dcaac4b12

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V → Prop)
    (hdown : ∀ {G H : SimpleGraph V}, G ≤ H → P H → P G)
    (L : SimpleGraph V) (hL : P L) :
    ∃ K : SimpleGraph V, L ≤ K ∧ P K ∧
      ∀ H : SimpleGraph V, K ≤ H → P H → H = K := by
  obtain ⟨K, hLK, hK⟩ := Finite.exists_le_maximal (p := P) hL
  exact ⟨K, hLK, hK.prop, fun H hKH hH => le_antisymm (hK.2 hH hKH) hKH⟩
