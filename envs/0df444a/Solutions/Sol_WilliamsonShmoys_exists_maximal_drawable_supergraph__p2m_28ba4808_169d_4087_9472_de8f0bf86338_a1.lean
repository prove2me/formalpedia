-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_28ba4808_169d_4087_9472_de8f0bf86338_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:44:09.435423+00:00
-- url     : https://prove2.me/submissions/0a52d09d-3dd3-47f8-8993-30b00fd718fe

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : HasPlanarDrawingOn H) :
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    ∃ K : SimpleGraph V,
      letI : DecidableRel K.Adj := Classical.decRel K.Adj
      H ≤ K ∧ HasPlanarDrawingOn K ∧
      H.edgeFinset.card ≤ K.edgeFinset.card ∧
      (∀ L : SimpleGraph V,
        letI : DecidableRel L.Adj := Classical.decRel L.Adj
        K ≤ L → HasPlanarDrawingOn L → L ≤ K) := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => H ≤ G ∧ HasPlanarDrawingOn G
  have hS : S.Nonempty := by
    refine ⟨H, ?_⟩
    simp [S, hH]
  obtain ⟨K, hKS, hKmax⟩ :=
    S.exists_max_image (fun G : SimpleGraph V => G.edgeFinset.card) hS
  have hKdata : H ≤ K ∧ HasPlanarDrawingOn K := by
    simpa [S] using hKS
  refine ⟨K, hKdata.1, hKdata.2, ?_, ?_⟩
  · exact hKmax H (by simpa [S] using
      (show H ≤ H ∧ HasPlanarDrawingOn H from ⟨le_rfl, hH⟩))
  · intro L hKL hL
    have hLmem : L ∈ S := by
      simp [S, hKdata.1.trans hKL, hL]
    have hmax : L.edgeFinset.card ≤ K.edgeFinset.card := hKmax L hLmem
    have hmono : K.edgeFinset ⊆ L.edgeFinset :=
      SimpleGraph.edgeFinset_mono hKL
    have hcard : K.edgeFinset.card = L.edgeFinset.card :=
      le_antisymm (Finset.card_le_card hmono) hmax
    have hedges : K.edgeFinset = L.edgeFinset :=
      Finset.eq_of_subset_of_card_le hmono (by rw [hcard])
    have hgraph : K = L := SimpleGraph.edgeFinset_inj.mp hedges
    rw [← hgraph]
