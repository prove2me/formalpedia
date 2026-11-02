-- Prove2me | solution 1 for WilliamsonShmoys.finite_hereditary_graph_property_has_maximal_extension__p2m_70f84f17_dac3_4815_92df_56beadc09612_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:11:48.745315+00:00
-- url     : https://prove2.me/submissions/4b70f067-1a89-4082-aedd-8d69c8957e1e

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (N : SimpleGraph V) (P : SimpleGraph V → Prop)
    (hN : P N)
    (hhered : ∀ {G H : SimpleGraph V}, H ≤ G → P G → P H) :
    ∃ K : SimpleGraph V, N ≤ K ∧ P K ∧
      ∀ L : SimpleGraph V, K ≤ L → P L → L ≤ K := by
  classical
  let S : Set (SimpleGraph V) := {G | N ≤ G ∧ P G}
  have hSfinite : S.Finite := Set.toFinite S
  have hNmem : N ∈ S := ⟨le_rfl, hN⟩
  obtain ⟨K, hNK, hKmax⟩ := hSfinite.exists_le_maximal hNmem
  refine ⟨K, hNK, hKmax.prop.2, ?_⟩
  intro L hKL hPL
  have hLmem : L ∈ S := ⟨le_trans hNK hKL, hPL⟩
  exact le_of_eq (hKmax.eq_of_le hLmem hKL).symm