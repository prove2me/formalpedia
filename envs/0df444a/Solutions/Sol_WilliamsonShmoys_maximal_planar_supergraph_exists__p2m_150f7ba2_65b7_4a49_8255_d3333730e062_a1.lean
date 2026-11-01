-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_150f7ba2_65b7_4a49_8255_d3333730e062_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:16:12.045618+00:00
-- url     : https://prove2.me/submissions/e6506af8-2dc9-45ad-b5bd-4219252f6ff2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      (∀ u v, H.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V,
        (∀ u v, K.Adj u v → L.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn L → L = K) := by
  classical
  let s : Set (SimpleGraph V) :=
    {G | H ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G}
  have hs : s.Finite := Set.toFinite _
  have hHmem : H ∈ s := ⟨le_rfl, hH⟩
  obtain ⟨K, hHK, hKmax⟩ := Finite.exists_le_maximal (p := fun G : SimpleGraph V => G ∈ s) hHmem
  refine ⟨K, ?_, hKmax.prop.2, ?_⟩
  · intro u v huv
    exact hHK huv
  · intro L hKL hL
    have hKLle : K ≤ L := fun {u v} huv => hKL u v huv
    have hLmem : L ∈ s := ⟨hHK.trans hKLle, hL⟩
    exact (hKmax.eq_of_le hLmem hKLle).symm