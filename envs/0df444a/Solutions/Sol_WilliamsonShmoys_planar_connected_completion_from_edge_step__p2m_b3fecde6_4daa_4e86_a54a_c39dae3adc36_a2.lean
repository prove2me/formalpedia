-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_completion_from_edge_step__p2m_b3fecde6_4daa_4e86_a54a_c39dae3adc36_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:50:22.57687+00:00
-- url     : https://prove2.me/submissions/a62895ab-8895-476a-8bd7-d49a2005d23c

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V → Prop)
    (H : SimpleGraph V) (hP : P H)
    (step : ∀ G : SimpleGraph V, P G → ¬ G.Connected →
      ∃ K : SimpleGraph V,
        G ≤ K ∧ P K ∧ ∃ u v, ¬ G.Reachable u v ∧ K.Adj u v) :
    ∃ K : SimpleGraph V, H ≤ K ∧ K.Connected ∧ P K := by
  classical
  let S : Finset (SimpleGraph V) := Finset.univ.filter fun G => H ≤ G ∧ P G
  have hS : S.Nonempty := by
    refine ⟨H, Finset.mem_filter.mpr ?_⟩
    simp [S, hP]
  obtain ⟨K, hKS, hmax⟩ :=
    Finset.exists_max_image S (fun G => G.edgeFinset.card) hS
  have hHK : H ≤ K := (Finset.mem_filter.mp hKS).2.1
  have hPK : P K := (Finset.mem_filter.mp hKS).2.2
  refine ⟨K, hHK, ?_, hPK⟩
  by_contra hKconn
  obtain ⟨K', hKK', hPK', u, v, hnotreach, hadj⟩ := step K hPK hKconn
  have hK'mem : K' ∈ S := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ K', ?_⟩
    exact ⟨le_trans hHK hKK', hPK'⟩
  have hlt : K < K' := by
    apply lt_of_le_of_ne hKK'
    intro heq
    subst K'
    exact False.elim (hnotreach (SimpleGraph.Adj.reachable hadj))
  have hcard : K.edgeFinset.card < K'.edgeFinset.card := by
    exact Finset.card_lt_card (SimpleGraph.edgeFinset_strict_mono hlt)
  exact (not_le_of_gt hcard) (hmax K' hK'mem)