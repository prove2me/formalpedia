-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawing_extend_to_inclusion_maximal
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:02:56.489933+00:00
-- url     : https://prove2.me/submissions/6a3ba30d-c52f-4f63-8b01-aa83f4650ffe

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      Set.Subset G.edgeSet H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        Set.Subset H.edgeSet K.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        Set.Subset K.edgeSet H.edgeSet := by
  classical
  let admissible : SimpleGraph V → Prop := fun H =>
    Set.Subset G.edgeSet H.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn H
  let candidates : Finset (SimpleGraph V) := Finset.univ.filter admissible
  have hnonempty : candidates.Nonempty := by
    refine ⟨G, Finset.mem_filter.mpr ?_⟩
    exact ⟨Finset.mem_univ G, Set.Subset.rfl, hG⟩
  obtain ⟨H, hHmem, hmax⟩ :=
    Finset.exists_max_image candidates (fun X => X.edgeFinset.card) hnonempty
  have hH : admissible H := (Finset.mem_filter.mp hHmem).2
  refine ⟨H, hH.1, hH.2, ?_⟩
  intro K hHK hK
  have hKmem : K ∈ candidates := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ K, ?_⟩
    exact ⟨fun e he => hHK (hH.1 he), hK⟩
  have hHKfin : H.edgeFinset ⊆ K.edgeFinset := by
    intro e he
    rw [SimpleGraph.mem_edgeFinset] at he ⊢
    exact hHK he
  have hcard : K.edgeFinset.card ≤ H.edgeFinset.card := hmax K hKmem
  have heq : H.edgeFinset = K.edgeFinset :=
    Finset.eq_of_subset_of_card_le hHKfin hcard
  intro e he
  have heK : e ∈ K.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset]
    exact he
  rw [← heq] at heK
  rw [SimpleGraph.mem_edgeFinset] at heK
  exact heK
