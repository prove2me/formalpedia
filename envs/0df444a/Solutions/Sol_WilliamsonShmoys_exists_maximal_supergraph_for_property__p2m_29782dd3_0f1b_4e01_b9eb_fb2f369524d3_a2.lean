-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_supergraph_for_property__p2m_29782dd3_0f1b_4e01_b9eb_fb2f369524d3_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:26:01.116951+00:00
-- url     : https://prove2.me/submissions/07e78121-71e2-4d1c-81bd-4584bbd36367

import Mathlib

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (Q : SimpleGraph V → Prop) (hM : Q M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ Q N ∧
      (∀ K : SimpleGraph V, M ≤ K → Q K →
        K.edgeSet.ncard ≤ N.edgeSet.ncard) := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter fun K => M ≤ K ∧ Q K
  have hS : S.Nonempty := by
    refine ⟨M, ?_⟩
    simp [S, hM]
  obtain ⟨N, hN, hmax⟩ :=
    Finset.exists_max_image S (fun K => K.edgeSet.ncard) hS
  refine ⟨N, ?_⟩
  have hNmem := Finset.mem_filter.mp hN
  refine ⟨hNmem.2.1, hNmem.2.2, ?_⟩
  intro K hMK hQK
  apply hmax K
  simp [S, hMK, hQK]