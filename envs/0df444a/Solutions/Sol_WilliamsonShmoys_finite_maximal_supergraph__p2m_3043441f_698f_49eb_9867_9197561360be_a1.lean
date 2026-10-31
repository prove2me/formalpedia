-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_supergraph__p2m_3043441f_698f_49eb_9867_9197561360be_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:39:11.545016+00:00
-- url     : https://prove2.me/submissions/0bd41f07-09b3-4a08-aed1-c2e66738af64

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hH : P H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ P K ∧
        ∀ L : SimpleGraph V, K ≤ L → P L → L = K := by
  classical
  let S : Set (SimpleGraph V) := {K | H ≤ K ∧ P K}
  have hSfinite : S.Finite := Set.toFinite S
  obtain ⟨K, hKS, hKmax⟩ := hSfinite.exists_maximal ⟨H, le_rfl, hH⟩
  refine ⟨K, hKS.1, hKS.2, ?_⟩
  intro L hKL hPL
  have hLS : L ∈ S := ⟨hKS.1.trans hKL, hPL⟩
  have hLK : L ≤ K := hKmax hLS hKL
  exact le_antisymm hLK hKL