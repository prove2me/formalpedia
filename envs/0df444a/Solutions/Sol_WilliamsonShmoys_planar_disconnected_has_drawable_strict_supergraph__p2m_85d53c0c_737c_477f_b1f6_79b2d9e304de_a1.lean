-- Prove2me | solution 1 for WilliamsonShmoys.planar_disconnected_has_drawable_strict_supergraph__p2m_85d53c0c_737c_477f_b1f6_79b2d9e304de_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:42:37.467291+00:00
-- url     : https://prove2.me/submissions/9eada465-b7b9-4caa-9590-50a356009c39
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_disconnected_has_separated_vertices__p2m_f334ebf7_af6a_4731_b73d_7440fcdb3338_a1
import Theorems.Thm_WilliamsonShmoys_planar_add_edge_across_components__p2m_f334ebf7_af6a_4731_b73d_7440fcdb3338_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 2 ≤ Fintype.card V)
    (hNot : ¬ K.Connected) :
    ∃ M : SimpleGraph V,
      K ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ M ≠ K := by
  obtain ⟨u, v, huv, hNonadj, hreach⟩ :=
    WilliamsonShmoys.planar_disconnected_has_separated_vertices__p2m_f334ebf7_af6a_4731_b73d_7440fcdb3338_a1
      K hCard hNot
  obtain ⟨M, hKM, huvM, hMDraw⟩ :=
    WilliamsonShmoys.planar_add_edge_across_components__p2m_f334ebf7_af6a_4731_b73d_7440fcdb3338_a1
      K hDraw u v huv hreach
  refine ⟨M, hKM, hMDraw, ?_⟩
  intro hEq
  exact hNonadj (hEq ▸ huvM)