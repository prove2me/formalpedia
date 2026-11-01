-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_supergraph_of_finite__p2m_6da47f0d_a7ea_48c9_976b_3e23d82be4ec_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:57:57.68345+00:00
-- url     : https://prove2.me/submissions/025f8bc9-ec55-411d-906d-9cac06dc0c8c

import Mathlib

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (H : SimpleGraph V)
    (hH : P H)
    (hmono : ∀ {G K : SimpleGraph V}, G ≤ K → P K → P G) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ P K ∧
        ∀ L : SimpleGraph V, K ≤ L → P L → L ≤ K := by
  classical
  obtain ⟨K, hHK, hKmax⟩ :=
    Finite.exists_le_maximal (a := H)
      (p := fun K : SimpleGraph V => H ≤ K ∧ P K)
      ⟨le_rfl, hH⟩
  refine ⟨K, hHK, hKmax.1.2, ?_⟩
  intro L hKL hPL
  exact hKmax.2 ⟨hHK.trans hKL, hPL⟩ hKL