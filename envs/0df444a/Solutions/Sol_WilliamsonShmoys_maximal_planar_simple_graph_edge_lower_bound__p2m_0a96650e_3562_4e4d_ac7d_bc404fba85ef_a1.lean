-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_simple_graph_edge_lower_bound__p2m_0a96650e_3562_4e4d_ac7d_bc404fba85ef_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:03:18.947313+00:00
-- url     : https://prove2.me/submissions/4727abad-d001-4714-9f49-d578ba918d1e

import Theorems.Thm_WilliamsonShmoys_drawable_edge_augmentation_below_planar_bound__p2m_54520c23_fb0c_40a7_a4c0_ad4b1f033824_a1__p2m_54520c23_fb0c_40a7_a4c0_ad4b1f033824_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ K : SimpleGraph V, N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = N) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj; 3 * Fintype.card V - 6 ≤ N.edgeFinset.card) := by
  classical
  by_contra hbound
  have hsmall : (letI : DecidableRel N.Adj := Classical.decRel N.Adj; N.edgeFinset.card) < 3 * Fintype.card V - 6 := Nat.lt_of_not_ge hbound
  obtain ⟨K, hle, hne, hdrawK⟩ :=
    WilliamsonShmoys.drawable_edge_augmentation_below_planar_bound__p2m_54520c23_fb0c_40a7_a4c0_ad4b1f033824_a1__p2m_54520c23_fb0c_40a7_a4c0_ad4b1f033824_a2
      N hcard hN hsmall
  have heq : K = N := hmax K hle hdrawK
  exact hne heq