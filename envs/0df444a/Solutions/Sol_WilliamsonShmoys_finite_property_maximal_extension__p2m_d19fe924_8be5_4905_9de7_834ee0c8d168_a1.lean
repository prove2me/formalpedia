-- Prove2me | solution 1 for WilliamsonShmoys.finite_property_maximal_extension__p2m_d19fe924_8be5_4905_9de7_834ee0c8d168_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T22:03:10.31031+00:00
-- url     : https://prove2.me/submissions/21048f72-444c-4509-826a-25f6c07ad754

import Mathlib

set_option maxHeartbeats 1000000 in
theorem solution
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : P H) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      (letI : DecidableRel K.Adj := dK
       P K ∧
       (∀ (L : SimpleGraph V) [DecidableRel L.Adj],
         P L →
         K.edgeFinset ⊆ L.edgeFinset →
         K.edgeFinset = L.edgeFinset) ∧
       H.edgeFinset ⊆ K.edgeFinset) := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => P G ∧ H ≤ G
  let C : Finset ℕ := S.image fun G => G.edgeSet.ncard
  have hC : C.Nonempty := by
    refine ⟨H.edgeSet.ncard, ?_⟩
    change H.edgeSet.ncard ∈ S.image (fun G => G.edgeSet.ncard)
    apply Finset.mem_image.mpr
    refine ⟨H, Finset.mem_filter.mpr ⟨Finset.mem_univ H, hH, le_rfl⟩, rfl⟩
  let m : ℕ := C.max' hC
  have hm : m ∈ C := Finset.max'_mem C hC
  obtain ⟨K, hKS, hKcard⟩ := Finset.mem_image.mp hm
  have hKprops : P K ∧ H ≤ K := (Finset.mem_filter.mp hKS).2
  have hKmax (L : SimpleGraph V) (hPL : P L) (hHL : H ≤ L) :
      L.edgeSet.ncard ≤ K.edgeSet.ncard := by
    have hLC : L.edgeSet.ncard ∈ C := by
      change L.edgeSet.ncard ∈ S.image (fun G => G.edgeSet.ncard)
      apply Finset.mem_image.mpr
      exact ⟨L, Finset.mem_filter.mpr ⟨Finset.mem_univ L, hPL, hHL⟩, rfl⟩
    have hLm : L.edgeSet.ncard ≤ m := by
      simpa [m] using (Finset.le_max' C L.edgeSet.ncard hLC)
    rw [hKcard]
    exact hLm
  refine ⟨K, Classical.decRel _, ?_⟩
  refine ⟨hKprops.1, ?_, ?_⟩
  · intro L dL hPL hKL
    letI : DecidableRel K.Adj := Classical.decRel _
    letI : DecidableRel L.Adj := dL
    have hKLorder : K ≤ L :=
      (SimpleGraph.edgeFinset_subset_edgeFinset).1 hKL
    have hHL : H ≤ L := hKprops.2.trans hKLorder
    have hcard : L.edgeSet.ncard ≤ K.edgeSet.ncard := hKmax L hPL hHL
    have hKLedges : K.edgeSet ⊆ L.edgeSet := SimpleGraph.edgeSet_mono hKLorder
    have hsets : K.edgeSet = L.edgeSet :=
      Set.eq_of_subset_of_ncard_le hKLedges hcard
    apply Finset.ext
    intro e
    simp only [SimpleGraph.mem_edgeFinset]
    rw [hsets]
  · intro e he
    have heH : e ∈ H.edgeSet := by
      simpa only [SimpleGraph.mem_edgeFinset] using he
    have heK : e ∈ K.edgeSet := SimpleGraph.edgeSet_mono hKprops.2 heH
    simpa only [SimpleGraph.mem_edgeFinset] using heK
