-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_e844fca5_030a_4b1e_8670_0e19dfc2fff4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:23:31.371461+00:00
-- url     : https://prove2.me/submissions/0ac340e7-7eaa-407c-8380-1ab471d780a3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) ∧
      (letI : DecidableRel H.Adj := dH
       letI : DecidableRel K.Adj := dK
       H.edgeFinset.card ≤ K.edgeFinset.card) := by
  classical
  let s : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => H ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  have hHmem : H ∈ s := by
    simp [s, hH]
  obtain ⟨K, hKmem, hKmax⟩ :=
    Finset.exists_max_image s (fun G => G.edgeFinset.card) ⟨H, hHmem⟩
  let dK : DecidableRel K.Adj := Classical.decRel K.Adj
  have hHK : H ≤ K := (Finset.mem_filter.mp hKmem).2.1
  have hKplanar : WilliamsonShmoys.HasPlanarDrawingOn K :=
    (Finset.mem_filter.mp hKmem).2.2
  have hmaximal : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by
    intro L hKL hLplanar
    have hLmem : L ∈ s := by
      simp [s, hHK.trans hKL, hLplanar]
    have hle : L.edgeFinset.card ≤ K.edgeFinset.card := hKmax L hLmem
    have hedge : K.edgeFinset = L.edgeFinset :=
      Finset.eq_of_subset_of_card_le
        (SimpleGraph.edgeFinset_subset_edgeFinset.mpr hKL) hle
    have hLK : L ≤ K :=
      SimpleGraph.edgeFinset_subset_edgeFinset.mp hedge.symm.subset
    exact le_antisymm hLK hKL
  have hcard :
      (letI : DecidableRel H.Adj := dH
       letI : DecidableRel K.Adj := dK
       H.edgeFinset.card ≤ K.edgeFinset.card) := by
    letI : DecidableRel H.Adj := dH
    letI : DecidableRel K.Adj := dK
    exact Finset.card_le_card
      (SimpleGraph.edgeFinset_subset_edgeFinset.mpr hHK)
  exact ⟨K, dK, hHK, hKplanar, hmaximal, hcard⟩
