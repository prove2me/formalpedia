-- Prove2me | solution 1 for WilliamsonShmoys.maximal_extension_of_predicate__p2m_69d74bef_9aa8_40b9_8469_f44173b0c825_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:23:13.722796+00:00
-- url     : https://prove2.me/submissions/87d6bdc4-4e8d-4124-8050-2b8308bf0bd8

import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop) (K : SimpleGraph V) (hK : P K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ P L ∧
        ∀ M : SimpleGraph V, P M → L ≤ M → M = L := by
  classical
  let s : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => K ≤ G ∧ P G
  have hs : s.Nonempty := by
    refine ⟨K, ?_⟩
    simp [s, hK]
  obtain ⟨L, hLs, hmax⟩ :=
    s.exists_max_image (fun G => G.edgeFinset.card) hs
  have hL : K ≤ L ∧ P L := (Finset.mem_filter.mp hLs).2
  refine ⟨L, hL.1, hL.2, ?_⟩
  intro M hM hLM
  have hKM : K ≤ M := hL.1.trans hLM
  have hMs : M ∈ s := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ M, hKM, hM⟩
  have hEdgesLM : L.edgeFinset ⊆ M.edgeFinset :=
    SimpleGraph.edgeFinset_subset_edgeFinset.mpr hLM
  have hEdges : L.edgeFinset = M.edgeFinset :=
    Finset.eq_of_subset_of_card_le hEdgesLM (hmax M hMs)
  exact SimpleGraph.edgeFinset_inj.mp hEdges.symm