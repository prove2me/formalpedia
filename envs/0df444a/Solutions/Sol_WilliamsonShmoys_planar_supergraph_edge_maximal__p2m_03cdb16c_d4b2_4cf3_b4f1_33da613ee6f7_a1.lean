-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_edge_maximal__p2m_03cdb16c_d4b2_4cf3_b4f1_33da613ee6f7_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:48:22.342986+00:00
-- url     : https://prove2.me/submissions/a03be3aa-bf5f-465c-be09-fa32de041bdf

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V, M ≤ K → HasPlanarDrawingOn K →
        (letI : DecidableRel K.Adj := Classical.decRel K.Adj
         letI : DecidableRel N.Adj := Classical.decRel N.Adj
         K.edgeFinset.card ≤ N.edgeFinset.card) := by
  classical
  let score : SimpleGraph V → Nat := fun G =>
    letI : DecidableRel G.Adj := Classical.decRel G.Adj
    G.edgeFinset.card
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => M ≤ G ∧ HasPlanarDrawingOn G
  have hS : S.Nonempty := by
    refine ⟨M, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact ⟨le_rfl, hM⟩
  obtain ⟨N, hNmem, hNmax⟩ := Finset.exists_max_image S score hS
  refine ⟨N, (Finset.mem_filter.mp hNmem).2.1,
    (Finset.mem_filter.mp hNmem).2.2, ?_⟩
  intro K hMK hK
  have hKmem : K ∈ S := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMK, hK⟩
  simpa [score] using hNmax K hKmem