-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_a419e21a_2978_404e_8b1f_5dd1d0da8bd8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:11:17.896265+00:00
-- url     : https://prove2.me/submissions/76e7e84f-ac04-43c9-9492-ac18777d03fa

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V,
      N.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K.edgeSet ⊂ L.edgeSet →
        ¬ WilliamsonShmoys.HasPlanarDrawingOn L := by
  classical
  let S : Finset (SimpleGraph V) := Finset.univ.filter fun K =>
    N.edgeSet ⊆ K.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn K
  have hNmem : N ∈ S := by
    simp [S, hN]
  obtain ⟨K, hKmem, hKmax⟩ :=
    Finset.exists_max_image S (fun K => Fintype.card K.edgeSet) ⟨N, hNmem⟩
  have hKmem' : N.edgeSet ⊆ K.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by
    simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hKmem
  refine ⟨K, hKmem'.1, hKmem'.2, ?_⟩
  intro L hKL hLdraw
  have hNL : N.edgeSet ⊆ L.edgeSet := hKmem'.1.trans hKL.1
  have hLmem : L ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hNL, hLdraw⟩
  have hcard : Fintype.card L.edgeSet ≤ Fintype.card K.edgeSet := hKmax L hLmem
  have hlt : Fintype.card K.edgeSet < Fintype.card L.edgeSet := Set.card_lt_card hKL
  omega