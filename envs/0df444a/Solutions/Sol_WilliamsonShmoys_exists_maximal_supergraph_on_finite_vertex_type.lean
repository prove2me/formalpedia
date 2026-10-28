-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_supergraph_on_finite_vertex_type
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:54:38.591847+00:00
-- url     : https://prove2.me/submissions/e620a4a6-ccdd-41da-8666-6905d48e7d8d

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (N : SimpleGraph V)
    (hP : P N) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ P K ∧
      (∀ L : SimpleGraph V, K ≤ L → P L → L = K) := by
  classical
  let Q : SimpleGraph V → Prop := fun G => N ≤ G ∧ P G
  have hQ : ∃ G : SimpleGraph V, Q G := ⟨N, le_rfl, hP⟩
  obtain ⟨K, dK, hK⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists Q).2 hQ
  letI := dK
  refine ⟨K, hK.1.1, hK.1.2, ?_⟩
  intro L hKL hPL
  exact ((SimpleGraph.IsExtremal.le_iff_eq hK ⟨le_trans hK.1.1 hKL, hPL⟩).mp hKL).symm