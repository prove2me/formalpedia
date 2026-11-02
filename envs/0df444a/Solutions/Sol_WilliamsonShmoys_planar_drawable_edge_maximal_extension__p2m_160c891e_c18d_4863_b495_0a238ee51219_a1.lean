-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawable_edge_maximal_extension__p2m_160c891e_c18d_4863_b495_0a238ee51219_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:38:59.684889+00:00
-- url     : https://prove2.me/submissions/2a89d45c-d250-42f2-8474-be5692506555

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧
      (∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K →
        (letI : DecidableRel K.Adj := Classical.decRel K.Adj
         letI : Fintype ↥K.edgeSet := Fintype.ofFinite _
         letI : DecidableRel N.Adj := Classical.decRel N.Adj
         letI : Fintype ↥N.edgeSet := Fintype.ofFinite _
         K.edgeFinset.card ≤ N.edgeFinset.card)) := by
  classical
  letI : Fintype (SimpleGraph V) := Fintype.ofFinite _
  let P : SimpleGraph V → Prop := fun G => M ≤ G ∧ HasPlanarDrawingOn G
  let f : SimpleGraph V → Nat := fun G => by
    letI : DecidableRel G.Adj := Classical.decRel G.Adj
    letI : Fintype ↥G.edgeSet := Fintype.ofFinite _
    exact G.edgeFinset.card
  let S : Finset (SimpleGraph V) := Finset.univ.filter P
  have hS : S.Nonempty := by
    refine ⟨M, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact ⟨le_rfl, hM⟩
  obtain ⟨N, hNmem, hNmax⟩ := Finset.exists_max_image S f hS
  have hNP : P N := (Finset.mem_filter.mp hNmem).2
  refine ⟨N, hNP.1, hNP.2, ?_⟩
  intro K hNK hK
  have hKmem : K ∈ S := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact ⟨le_trans hNP.1 hNK, hK⟩
  have hcard := hNmax K hKmem
  simpa [f] using hcard
