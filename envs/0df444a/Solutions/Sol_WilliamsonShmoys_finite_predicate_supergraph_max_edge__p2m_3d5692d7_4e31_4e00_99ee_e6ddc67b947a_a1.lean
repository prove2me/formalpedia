-- Prove2me | solution 1 for WilliamsonShmoys.finite_predicate_supergraph_max_edge__p2m_3d5692d7_4e31_4e00_99ee_e6ddc67b947a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:32:51.039333+00:00
-- url     : https://prove2.me/submissions/b65a1ee3-0f43-41c8-814b-998320ed0581

import Mathlib

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V → Prop) (H : SimpleGraph V) (hP : P H)
    (hereditary : ∀ ⦃G K : SimpleGraph V⦄, G ≤ K → P K → P G) :
    ∃ K : SimpleGraph V, H ≤ K ∧ P K ∧
      ∀ L : SimpleGraph V, H ≤ L → P L → L.edgeSet.ncard ≤ K.edgeSet.ncard := by
  classical
  let candidates : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun K => H ≤ K ∧ P K)
  have candidates_nonempty : candidates.Nonempty := by
    refine ⟨H, ?_⟩
    simp [candidates, hP]
  obtain ⟨K, hK, hmax⟩ :=
    Finset.exists_max_image candidates (fun L => L.edgeSet.ncard) candidates_nonempty
  have hK' : H ≤ K ∧ P K := (Finset.mem_filter.mp hK).2
  refine ⟨K, hK'.1, hK'.2, ?_⟩
  intro L hHL hPL
  have hL : L ∈ candidates := by
    simp [candidates, hHL, hPL]
  exact hmax L hL