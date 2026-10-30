-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_planar_extension__p2m_04c2f104_e4e1_4da1_bff1_5e666d9628dd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:37:16.07265+00:00
-- url     : https://prove2.me/submissions/7377556b-2d6a-49d2-b70b-2b2818c3ace9

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      Set.Subset G.edgeSet H.edgeSet ∧
      ∀ K : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn K →
        Set.Subset H.edgeSet K.edgeSet →
        H.edgeSet = K.edgeSet := by
  classical
  letI : Fintype (SimpleGraph V) := Fintype.ofFinite (SimpleGraph V)
  let admissible : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun H =>
      WilliamsonShmoys.HasPlanarDrawingOn H ∧ Set.Subset G.edgeSet H.edgeSet)
  have hGmem : G ∈ admissible := by
    simp only [admissible, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hG, Set.Subset.rfl⟩
  obtain ⟨H, hHmem, hHmax⟩ :=
    Finset.exists_max_image admissible (fun H => H.edgeFinset.card) ⟨G, hGmem⟩
  have hHprop : WilliamsonShmoys.HasPlanarDrawingOn H ∧
      Set.Subset G.edgeSet H.edgeSet := by
    simpa [admissible] using hHmem
  refine ⟨H, hHprop.1, hHprop.2, ?_⟩
  intro K hK hHK
  have hGK : Set.Subset G.edgeSet K.edgeSet := hHprop.2.trans hHK
  have hKmem : K ∈ admissible := by
    simp [admissible, hK, hGK]
  have hKcard : K.edgeFinset.card ≤ H.edgeFinset.card := hHmax K hKmem
  have hHsub : H.edgeFinset ⊆ K.edgeFinset := by
    intro e he
    rw [SimpleGraph.mem_edgeFinset] at he ⊢
    exact hHK he
  have hHcard : H.edgeFinset.card ≤ K.edgeFinset.card := Finset.card_le_card hHsub
  have hEdgeEq : H.edgeFinset = K.edgeFinset :=
    Finset.eq_of_subset_of_card_le hHsub hKcard
  have hGraphEq : H = K := SimpleGraph.edgeFinset_inj.mp hEdgeEq
  rw [hGraphEq]