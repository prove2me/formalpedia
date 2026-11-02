-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_supergraph_for_predicate__p2m_7202bf9d_a814_4b20_b0a7_1713c12fe256_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:49:21.322014+00:00
-- url     : https://prove2.me/submissions/8af795d6-0f35-488d-9b25-21a041c7225c

import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_maximal_mem_finset__p2m_5361ebef_f1bf_4ddf_9929_f0777c6d31bd_a1
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] (P : SimpleGraph V → Prop) (G : SimpleGraph V)
    (hG : P G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ P H ∧
      (∀ K : SimpleGraph V, P K → H ≤ K → K ≤ H) := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun H => G ≤ H ∧ P H)
  have hS : S.Nonempty := by
    refine ⟨G, ?_⟩
    simp [S, hG]
  obtain ⟨H, hH, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_mem_finset__p2m_5361ebef_f1bf_4ddf_9929_f0777c6d31bd_a1 S hS
  refine ⟨H, ?_, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hH).2.1
  · exact (Finset.mem_filter.mp hH).2.2
  · intro K hK hHK
    apply hmax K
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ K, ⟨le_trans (Finset.mem_filter.mp hH).2.1 hHK, hK⟩⟩
    · exact hHK