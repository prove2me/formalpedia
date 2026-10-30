-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_maximal_drawable_supergraph__p2m_d5ea2124_1838_4ceb_a0a8_373ec58ed0bb_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:48:12.234346+00:00
-- url     : https://prove2.me/submissions/0c86a7d0-0bf8-45fc-9f1a-0cea6d71dfd8

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hDraw : HasPlanarDrawingOn H) :
    Exists fun K : SimpleGraph V =>
      And (Set.Subset H.edgeSet K.edgeSet)
        (And (HasPlanarDrawingOn K)
          (forall L : SimpleGraph V,
            Set.Subset K.edgeSet L.edgeSet ->
            HasPlanarDrawingOn L ->
            Set.Subset L.edgeSet K.edgeSet)) := by
  classical
  let admissible : Finset (SimpleGraph V) := Finset.univ.filter fun K =>
    And (Set.Subset H.edgeSet K.edgeSet) (HasPlanarDrawingOn K)
  have hnonempty : admissible.Nonempty := by
    refine ⟨H, ?_⟩
    simp only [admissible, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨(fun _ he => he), hDraw⟩
  let hmaxExists :=
    Finset.exists_max_image admissible (fun G : SimpleGraph V => G.edgeFinset.card) hnonempty
  let K : SimpleGraph V := hmaxExists.choose
  have hKmem : K ∈ admissible := hmaxExists.choose_spec.1
  have hKmax : ∀ L : SimpleGraph V, L ∈ admissible →
      L.edgeFinset.card ≤ K.edgeFinset.card := hmaxExists.choose_spec.2
  have hKH : Set.Subset H.edgeSet K.edgeSet := (Finset.mem_filter.mp hKmem).2.1
  have hKdraw : HasPlanarDrawingOn K := (Finset.mem_filter.mp hKmem).2.2
  refine ⟨K, hKH, hKdraw, ?_⟩
  intro L hKL hLdraw
  have hHL : Set.Subset H.edgeSet L.edgeSet := by
    intro e he
    exact hKL (hKH he)
  have hLmem : L ∈ admissible := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hHL, hLdraw⟩
  have hcard : L.edgeFinset.card ≤ K.edgeFinset.card := hKmax L hLmem
  have hsub : K.edgeFinset ⊆ L.edgeFinset := by
    intro e he
    rw [SimpleGraph.mem_edgeFinset] at he ⊢
    exact hKL he
  have heq : K.edgeFinset = L.edgeFinset :=
    Finset.eq_of_subset_of_card_le hsub hcard
  intro e he
  have heL : e ∈ L.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset]
    exact he
  have heK : e ∈ K.edgeFinset := by
    rw [heq]
    exact heL
  rw [SimpleGraph.mem_edgeFinset] at heK
  exact heK