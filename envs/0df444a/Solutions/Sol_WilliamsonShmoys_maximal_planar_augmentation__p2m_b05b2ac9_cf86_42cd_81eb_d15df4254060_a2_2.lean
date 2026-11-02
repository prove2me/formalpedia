-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_augmentation__p2m_b05b2ac9_cf86_42cd_81eb_d15df4254060_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T20:33:38.021803+00:00
-- url     : https://prove2.me/submissions/a0e08cc9-6a86-490e-b042-f33bf6b786bb

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       letI : DecidableRel K.Adj := Classical.decRel K.Adj
       H.edgeFinset.card ≤ K.edgeFinset.card) := by
  classical
  let eligible : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => H ≤ G ∧ HasPlanarDrawingOn G
  have hEligible : eligible.Nonempty := by
    refine ⟨H, Finset.mem_filter.mpr ?_⟩
    exact ⟨Finset.mem_univ _, le_rfl, hH⟩
  obtain ⟨K, hKmem, hKmax⟩ :=
    Finset.exists_max_image eligible (fun G => G.edgeFinset.card) hEligible
  have hHK : H ≤ K := (Finset.mem_filter.mp hKmem).2.1
  have hKplanar : HasPlanarDrawingOn K := (Finset.mem_filter.mp hKmem).2.2
  have hEdgeMax : ∀ G : SimpleGraph V, H ≤ G → HasPlanarDrawingOn G →
      G.edgeFinset.card ≤ K.edgeFinset.card := by
    intro G hHG hGplanar
    apply hKmax G
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hHG, hGplanar⟩
  have edge_count_eq {G L : SimpleGraph V} (hGL : G ≤ L)
      (hcard : L.edgeFinset.card ≤ G.edgeFinset.card) : L = G := by
    have hsubset : G.edgeFinset ⊆ L.edgeFinset := SimpleGraph.edgeFinset_mono hGL
    have hedge : G.edgeFinset = L.edgeFinset :=
      Finset.eq_of_subset_of_card_le hsubset hcard
    apply SimpleGraph.ext
    funext u v
    apply propext
    have hedgeUV : s(u, v) ∈ G.edgeFinset ↔ s(u, v) ∈ L.edgeFinset := by
      rw [hedge]
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hedgeUV.symm
  refine ⟨K, hHK, hKplanar, ?_, ?_⟩
  · intro L hKL hLplanar
    apply edge_count_eq hKL
    exact hEdgeMax L (le_trans hHK hKL) hLplanar
  · exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hHK)
