-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_18dadb11_49a3_466e_95d7_24d3c5d5bdee_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:57:19.659141+00:00
-- url     : https://prove2.me/submissions/54ea2c69-8d1d-4e3d-9cc3-59cfafb62a75

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K := by
  classical
  let candidates : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => H ≤ G ∧ HasPlanarDrawingOn G
  have hCandidates : candidates.Nonempty := by
    refine ⟨H, Finset.mem_filter.mpr ?_⟩
    exact ⟨Finset.mem_univ H, le_rfl, hH⟩
  let scores : Finset ℕ := candidates.image fun G => G.edgeFinset.card
  have hScores : scores.Nonempty := hCandidates.image _
  let m : ℕ := scores.max' hScores
  have hm : m ∈ scores := by
    exact Finset.max'_mem scores hScores
  obtain ⟨K, hKmem, hKscore⟩ := Finset.mem_image.mp hm
  have hKprops : H ≤ K ∧ HasPlanarDrawingOn K :=
    (Finset.mem_filter.mp hKmem).2
  refine ⟨K, hKprops.1, hKprops.2, ?_⟩
  intro L hKL hLplanar
  have hLmem : L ∈ candidates := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ L, ⟨hKprops.1.trans hKL, hLplanar⟩⟩
  have hLscore : L.edgeFinset.card ≤ K.edgeFinset.card := by
    have hLscoreMem : L.edgeFinset.card ∈ scores :=
      Finset.mem_image.mpr ⟨L, hLmem, rfl⟩
    calc
      L.edgeFinset.card ≤ scores.max' hScores := by
        simpa using (Finset.le_max' scores L.edgeFinset.card hLscoreMem)
      _ = K.edgeFinset.card := hKscore.symm
  have hEdgeSubset : K.edgeFinset ⊆ L.edgeFinset :=
    SimpleGraph.edgeFinset_subset_edgeFinset.mpr hKL
  have hEdgeEq : K.edgeFinset = L.edgeFinset :=
    Finset.eq_of_subset_of_card_le hEdgeSubset hLscore
  exact SimpleGraph.edgeFinset_inj.mp hEdgeEq |>.symm