-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_extension__p2m_711cef84_2190_482b_bc2d_a11a812cbece_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:54:00.488961+00:00
-- url     : https://prove2.me/submissions/98ab196d-b7f5-443d-af45-75a60ea1f141

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L) :
    ∃ H : SimpleGraph V,
      HasPlanarDrawingOn H ∧
      (letI : DecidableRel L.Adj := Classical.decRel L.Adj
       letI : DecidableRel H.Adj := Classical.decRel H.Adj
       L.edgeFinset.card ≤ H.edgeFinset.card) ∧
      (∀ K : SimpleGraph V, HasPlanarDrawingOn K →
        (∀ u v, H.Adj u v → K.Adj u v) →
        ∀ u v, K.Adj u v → H.Adj u v) := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => HasPlanarDrawingOn G ∧ L ≤ G
  have hS : L ∈ S := by
    simp [S, hL]
  obtain ⟨H, hHmem, hmax⟩ :=
    Finset.exists_max_image S (fun G => G.edgeFinset.card) ⟨L, hS⟩
  have hdraw : HasPlanarDrawingOn H := (Finset.mem_filter.mp hHmem).2.1
  have hLH : L ≤ H := (Finset.mem_filter.mp hHmem).2.2
  refine ⟨H, hdraw, ?_, ?_⟩
  · have hLcard := hmax L hS
    simpa using hLcard
  · intro K hK hHK u v huv
    have hHK' : H ≤ K := hHK
    have hKH : K ≤ H := by
      by_contra hnot
      have hlt : H < K := ⟨hHK', hnot⟩
      have hproper : H.edgeFinset ⊂ K.edgeFinset :=
        (SimpleGraph.edgeFinset_ssubset_edgeFinset).2 hlt
      have hcard : H.edgeFinset.card < K.edgeFinset.card :=
        Finset.card_lt_card hproper
      have hLK : L ≤ K := le_trans hLH hHK'
      have hKmem : K ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hK, hLK⟩
      have hmaxK := hmax K hKmem
      omega
    exact hKH huv