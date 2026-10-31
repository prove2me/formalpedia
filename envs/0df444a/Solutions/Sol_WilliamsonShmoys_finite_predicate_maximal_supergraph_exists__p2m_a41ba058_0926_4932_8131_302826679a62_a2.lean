-- Prove2me | solution 1 for WilliamsonShmoys.finite_predicate_maximal_supergraph_exists__p2m_a41ba058_0926_4932_8131_302826679a62_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:14:21.545276+00:00
-- url     : https://prove2.me/submissions/0a07ae63-36ac-4e16-a4e5-1fe8e38693a4

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hG : P G)
    (hdown : ∀ {A B : SimpleGraph V}, A ≤ B → P B → P A) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ P K ∧ ∀ H : SimpleGraph V, K ≤ H → P H → H ≤ K := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter fun H => G ≤ H ∧ P H
  have hS : S.Nonempty := by
    refine ⟨G, ?_⟩
    simp [S, hG]
  obtain ⟨K, hK, hmax⟩ :=
    Finset.exists_max_image S (fun H => H.edgeFinset.card) hS
  have hKG : G ≤ K := (Finset.mem_filter.mp hK).2.1
  have hPK : P K := (Finset.mem_filter.mp hK).2.2
  refine ⟨K, hKG, hPK, ?_⟩
  intro H hKH hPH
  have hGH : G ≤ H := le_trans hKG hKH
  have hH : H ∈ S := by
    simp [S, hGH, hPH]
  have hcard : H.edgeFinset.card ≤ K.edgeFinset.card := hmax H hH
  have hedges : K.edgeFinset = H.edgeFinset :=
    Finset.eq_of_subset_of_card_le
      (SimpleGraph.edgeFinset_subset_edgeFinset.mpr hKH) hcard
  have hEq : K = H := SimpleGraph.edgeFinset_inj.mp hedges
  simpa [hEq]