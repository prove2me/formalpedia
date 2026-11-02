-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_supergraph_of_finite__p2m_f4b47241_0114_4ac8_84bb_0550b2f73838_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:55:07.795213+00:00
-- url     : https://prove2.me/submissions/9b463adc-0222-4bfd-9bee-7343e3d73abe

import Mathlib

theorem solution
    {V : Type} [Fintype V]
    (H : SimpleGraph V) (P : SimpleGraph V → Prop) (hP : P H) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj := fun K => Classical.decRel K.Adj
    ∃ K : SimpleGraph V, H ≤ K ∧ P K ∧
      ∀ L : SimpleGraph V, K ≤ L → P L → L = K := by
  classical
  obtain ⟨K, dK, hK⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists
      (fun K : SimpleGraph V => H ≤ K ∧ P K)).2
      ⟨H, le_rfl, hP⟩
  letI : DecidableRel K.Adj := dK
  refine ⟨K, hK.1.1, hK.1.2, ?_⟩
  intro L hKL hPL
  have hPred : H ≤ L ∧ P L := ⟨le_trans hK.1.1 hKL, hPL⟩
  exact ((SimpleGraph.IsExtremal.le_iff_eq hK hPred).mp hKL).symm