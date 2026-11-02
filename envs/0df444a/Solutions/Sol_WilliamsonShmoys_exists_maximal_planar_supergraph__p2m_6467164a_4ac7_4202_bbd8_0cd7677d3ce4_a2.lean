-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_6467164a_4ac7_4202_bbd8_0cd7677d3ce4_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:18:47.436228+00:00
-- url     : https://prove2.me/submissions/1bc3cd43-a1ec-48f2-a8c0-a7b13ac88805

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 <= Fintype.card V) :
    Exists fun H : SimpleGraph V =>
      And (N <= H)
        (And (WilliamsonShmoys.HasPlanarDrawingOn H)
          (forall K : SimpleGraph V,
            H <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K = H)) := by
  classical
  let S : Finset (SimpleGraph V) := Finset.univ.filter fun G =>
    N <= G ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  have hS : S.Nonempty := by
    refine ⟨N, ?_⟩
    simp [S, hN]
  obtain ⟨H, hHmem, hmax⟩ :=
    Finset.exists_max_image S (fun G : SimpleGraph V => G.edgeFinset.card) hS
  have hNH : N <= H := (Finset.mem_filter.mp hHmem).2.1
  have hHplanar : WilliamsonShmoys.HasPlanarDrawingOn H :=
    (Finset.mem_filter.mp hHmem).2.2
  refine ⟨H, hNH, hHplanar, ?_⟩
  intro K hHK hKplanar
  by_contra hKH
  have hKmem : K ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hNH.trans hHK, hKplanar⟩
  have hstrict : H < K := lt_of_le_of_ne hHK (Ne.symm hKH)
  have hcardlt : H.edgeFinset.card < K.edgeFinset.card := by
    exact Finset.card_lt_card
      ((SimpleGraph.edgeFinset_ssubset_edgeFinset).2 hstrict)
  exact (not_lt_of_ge (hmax K hKmem)) hcardlt