-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_supergraph_of_finite_predicate__p2m_a06f5bd4_9714_4d93_b157_09922cf717e8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:57:23.315383+00:00
-- url     : https://prove2.me/submissions/46deefc7-d16f-4c24-9b62-be3c8e3e38d5

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (P : SimpleGraph V → Prop) (hP : P H) :
    Exists fun K : SimpleGraph V =>
      And (LE.le H K) (And (P K)
        (forall L : SimpleGraph V, LE.le K L -> P L -> Eq L K)) := by
  classical
  let admissible : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => H ≤ G ∧ P G
  have h_admissible : admissible.Nonempty := by
    refine ⟨H, ?_⟩
    simp [admissible, hP]
  obtain ⟨K, hK_mem, hK_max⟩ :=
    Finset.exists_max_image admissible (fun G : SimpleGraph V => G.edgeFinset.card)
      h_admissible
  have hHK : H ≤ K := (Finset.mem_filter.mp hK_mem).2.1
  have hPK : P K := (Finset.mem_filter.mp hK_mem).2.2
  refine ⟨K, hHK, hPK, ?_⟩
  intro L hKL hPL
  have hL_mem : L ∈ admissible := by
    simp [admissible, le_trans hHK hKL, hPL]
  have hcard : L.edgeFinset.card ≤ K.edgeFinset.card := hK_max L hL_mem
  have hsubset : K.edgeFinset ⊆ L.edgeFinset :=
    SimpleGraph.edgeFinset_subset_edgeFinset.mpr hKL
  have hedge : K.edgeFinset = L.edgeFinset :=
    Finset.eq_of_subset_of_card_le hsubset hcard
  exact (SimpleGraph.edgeFinset_inj.mp hedge).symm