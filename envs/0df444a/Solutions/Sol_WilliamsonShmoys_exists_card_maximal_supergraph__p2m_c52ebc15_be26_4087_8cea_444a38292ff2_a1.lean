-- Prove2me | solution 1 for WilliamsonShmoys.exists_card_maximal_supergraph__p2m_c52ebc15_be26_4087_8cea_444a38292ff2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:26:26.386997+00:00
-- url     : https://prove2.me/submissions/4ce99a53-d911-4fd9-91a3-f1520c46f94c

import Mathlib

theorem solution
    {V : Type} [Fintype V]
    (N : SimpleGraph V) (P : SimpleGraph V → Prop) (hN : P N) :
    ∃ H : SimpleGraph V,
      N.edgeSet ⊆ H.edgeSet ∧ P H ∧
      (∀ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet → P K → K.edgeSet ⊆ H.edgeSet) ∧
      N.edgeSet.ncard ≤ H.edgeSet.ncard := by
  classical
  let s : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun G => N.edgeSet ⊆ G.edgeSet ∧ P G)
  have hs : s.Nonempty := by
    refine ⟨N, ?_⟩
    simp [s, hN]
  obtain ⟨H, hH, hHmax⟩ := Finset.exists_max_image s (fun G => G.edgeSet.ncard) hs
  have hHmem : N.edgeSet ⊆ H.edgeSet ∧ P H := by
    simpa [s] using hH
  refine ⟨H, hHmem.1, hHmem.2, ?_, ?_⟩
  · intro K hHK hPK
    have hNK : N.edgeSet ⊆ K.edgeSet := hHmem.1.trans hHK
    have hKmem : K ∈ s := by
      simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and] using And.intro hNK hPK
    have hcard : K.edgeSet.ncard ≤ H.edgeSet.ncard := hHmax K hKmem
    have hEq : H.edgeSet = K.edgeSet := Set.eq_of_subset_of_ncard_le hHK hcard
    exact hEq.symm.subset
  · have hNmem : N ∈ s := by
      simp [s, hN]
    exact hHmax N hNmem