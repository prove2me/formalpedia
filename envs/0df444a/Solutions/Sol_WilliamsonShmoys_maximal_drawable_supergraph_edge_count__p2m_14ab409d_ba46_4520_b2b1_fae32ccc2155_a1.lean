-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_supergraph_edge_count__p2m_14ab409d_ba46_4520_b2b1_fae32ccc2155_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:39:11.369107+00:00
-- url     : https://prove2.me/submissions/a6f72896-1fc6-441f-8315-18d9c144d5e3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_3a2fa668_af0b_4223_89b0_dcabec19097b_a1
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation__p2m_3a2fa668_af0b_4223_89b0_dcabec19097b_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (A N : SimpleGraph V)
    (hAN : A ≤ N)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet.ncard ≤ N.edgeSet.ncard) :
    N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hNK, hK, hKcount⟩ :=
    WilliamsonShmoys.planar_supergraph_triangulation__p2m_3a2fa668_af0b_4223_89b0_dcabec19097b_a1
      N hN hCard
  have hlow : 3 * Fintype.card V - 6 ≤ N.edgeSet.ncard := by
    have h := hmax K hNK hK
    rw [hKcount] at h
    exact h
  have hupp : N.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
    WilliamsonShmoys.planar_edge_count_upper_bound__p2m_3a2fa668_af0b_4223_89b0_dcabec19097b_a1
      N hN hCard
  omega