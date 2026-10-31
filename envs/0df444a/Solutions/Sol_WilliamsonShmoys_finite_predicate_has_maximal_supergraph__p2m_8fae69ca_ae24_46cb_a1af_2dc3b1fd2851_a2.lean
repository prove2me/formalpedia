-- Prove2me | solution 1 for WilliamsonShmoys.finite_predicate_has_maximal_supergraph__p2m_8fae69ca_ae24_46cb_a1af_2dc3b1fd2851_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:14:18.018985+00:00
-- url     : https://prove2.me/submissions/dd280889-819c-44e0-b2cc-4121271a5d8e

import Mathlib
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop) (N : SimpleGraph V) (hN : P N)
    (hdown : ∀ {A B : SimpleGraph V}, A ≤ B → P B → P A) :
    ∃ K : SimpleGraph V, N ≤ K ∧ N.edgeSet.ncard ≤ K.edgeSet.ncard ∧ P K ∧
      ∀ L : SimpleGraph V, K ≤ L → P L → L ≤ K := by
  classical
  let S : Set (SimpleGraph V) := {K | N ≤ K ∧ P K}
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := ⟨N, le_rfl, hN⟩
  obtain ⟨K, hKmax⟩ := hSfinite.exists_maximal hSnonempty
  have hKmem : K ∈ S := hKmax.1
  refine ⟨K, hKmem.1, ?_, hKmem.2, ?_⟩
  · exact Set.ncard_mono (SimpleGraph.edgeSet_mono hKmem.1)
  · intro L hKL hPL
    have hLmem : L ∈ S := ⟨hKmem.1.trans hKL, hPL⟩
    exact hKmax.2 hLmem hKL