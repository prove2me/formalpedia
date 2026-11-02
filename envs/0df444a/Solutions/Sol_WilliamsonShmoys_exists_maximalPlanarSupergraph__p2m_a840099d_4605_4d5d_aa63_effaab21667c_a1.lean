-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximalPlanarSupergraph__p2m_a840099d_4605_4d5d_aa63_effaab21667c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:46:14.413979+00:00
-- url     : https://prove2.me/submissions/9f09aefa-cba6-4960-a9c6-82d541847395

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : HasPlanarDrawingOn K) :
    ∃ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
      HasPlanarDrawingOn L ∧
      (letI : DecidableRel K.Adj := dK
       letI : DecidableRel L.Adj := dL
       K.edgeFinset ⊆ L.edgeFinset) ∧
      (∀ (M : SimpleGraph V) (dM : DecidableRel M.Adj),
        HasPlanarDrawingOn M →
        (letI : DecidableRel L.Adj := dL
         letI : DecidableRel M.Adj := dM
         L.edgeFinset ⊆ M.edgeFinset) →
        (letI : DecidableRel L.Adj := dL
         letI : DecidableRel M.Adj := dM
         L.edgeFinset = M.edgeFinset)) := by
  classical
  letI : DecidableRel K.Adj := dK
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G : SimpleGraph V =>
      HasPlanarDrawingOn G ∧ K.edgeSet ⊆ G.edgeSet
  have hS : S.Nonempty := by
    refine ⟨K, ?_⟩
    simp [S, hK]
  obtain ⟨L, hLmem, hLmax⟩ :=
    Finset.exists_max_image S
      (fun G : SimpleGraph V => (SimpleGraph.edgeFinset G).card) hS
  have hL : HasPlanarDrawingOn L := (Finset.mem_filter.mp hLmem).2.1
  have hKLset : K.edgeSet ⊆ L.edgeSet :=
    (Finset.mem_filter.mp hLmem).2.2
  let dL : DecidableRel L.Adj := fun a b => Classical.propDecidable (L.Adj a b)
  letI : DecidableRel L.Adj := dL
  have hKL : K.edgeFinset ⊆ L.edgeFinset := by
    intro e he
    exact SimpleGraph.mem_edgeFinset.mpr
      (hKLset (SimpleGraph.mem_edgeFinset.mp he))
  refine ⟨L, dL, hL, hKL, ?_⟩
  intro M dM hM hLM
  letI : DecidableRel M.Adj := dM
  have hLMset : L.edgeSet ⊆ M.edgeSet := by
    intro e he
    have heL : e ∈ L.edgeFinset := SimpleGraph.mem_edgeFinset.mpr he
    exact SimpleGraph.mem_edgeFinset.mp (hLM heL)
  have hMmem : M ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hM, hKLset.trans hLMset⟩
  have hcard :
      (letI : DecidableRel M.Adj := fun a b => Classical.propDecidable (M.Adj a b);
       M.edgeFinset.card) ≤ L.edgeFinset.card := by
    letI : DecidableRel M.Adj := fun a b => Classical.propDecidable (M.Adj a b)
    exact hLmax M hMmem
  have hsub :
      (letI : DecidableRel M.Adj := fun a b => Classical.propDecidable (M.Adj a b);
       L.edgeFinset ⊆ M.edgeFinset) := by
    letI : DecidableRel M.Adj := fun a b => Classical.propDecidable (M.Adj a b)
    intro e he
    exact SimpleGraph.mem_edgeFinset.mpr
      (hLMset (SimpleGraph.mem_edgeFinset.mp he))
  have hEq := Finset.eq_of_subset_of_card_le hsub hcard
  have hEqSet : L.edgeSet = M.edgeSet := by
    letI : DecidableRel M.Adj := fun a b => Classical.propDecidable (M.Adj a b)
    ext e
    have hiff : (e ∈ L.edgeFinset) ↔ (e ∈ M.edgeFinset) :=
      Iff.of_eq (congrArg (fun s : Finset (Sym2 V) => e ∈ s) hEq)
    simpa only [SimpleGraph.mem_edgeFinset] using hiff
  apply Finset.ext
  intro e
  have hiff : e ∈ L.edgeSet ↔ e ∈ M.edgeSet := by
    rw [hEqSet]
  simpa only [SimpleGraph.mem_edgeFinset] using hiff