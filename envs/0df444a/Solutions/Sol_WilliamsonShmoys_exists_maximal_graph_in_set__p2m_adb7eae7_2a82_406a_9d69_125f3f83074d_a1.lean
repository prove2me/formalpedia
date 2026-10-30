-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_graph_in_set__p2m_adb7eae7_2a82_406a_9d69_125f3f83074d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:29:20.299274+00:00
-- url     : https://prove2.me/submissions/a3eb611e-46c8-4d88-922f-5e3b42a0c2f1

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] (S : Set (SimpleGraph V)) (hne : S.Nonempty) :
    ∃ K ∈ S, ∀ L ∈ S, K ≤ L → L = K := by
  classical
  obtain ⟨K, hK⟩ := (Set.toFinite S).exists_maximal hne
  refine ⟨K, hK.1, ?_⟩
  intro L hLS hKL
  exact le_antisymm (hK.2 hLS hKL) hKL