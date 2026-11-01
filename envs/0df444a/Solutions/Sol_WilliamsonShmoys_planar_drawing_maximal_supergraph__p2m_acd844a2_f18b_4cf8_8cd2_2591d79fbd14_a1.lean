-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_acd844a2_f18b_4cf8_8cd2_2591d79fbd14_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:37:39.43102+00:00
-- url     : https://prove2.me/submissions/74c516ae-7b33-4653-bb4b-8ace0b8e68e5

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_simple_graph_type__p2m_4d05bb9d_42a1_4f6c_b6b4_be7b1a8f6d1e_a1
import Theorems.Thm_finite_family_maximum__p2m_4d05bb9d_42a1_4f6c_b6b4_be7b1a8f6d1e_a1
import Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono__p2m_4d05bb9d_42a1_4f6c_b6b4_be7b1a8f6d1e_a1
import Theorems.Thm_WilliamsonShmoys_eq_of_adj_and_edgeSet_ncard_le__p2m_4d05bb9d_42a1_4f6c_b6b4_be7b1a8f6d1e_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ H : SimpleGraph V,
      (∀ u v, L.Adj u v → H.Adj u v) ∧
      L.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V,
        (∀ u v, H.Adj u v → K.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn K → K = H) := by
  classical
  haveI : Finite (SimpleGraph V) :=
    WilliamsonShmoys.finite_simple_graph_type__p2m_4d05bb9d_42a1_4f6c_b6b4_be7b1a8f6d1e_a1
  letI : Fintype (SimpleGraph V) := Fintype.ofFinite (SimpleGraph V)
  let P : SimpleGraph V → Prop := fun G =>
    (∀ u v, L.Adj u v → G.Adj u v) ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  obtain ⟨H, hPH, hmax⟩ :=
    finite_family_maximum__p2m_4d05bb9d_42a1_4f6c_b6b4_be7b1a8f6d1e_a1
      P (fun G : SimpleGraph V => G.edgeSet.ncard)
      ⟨L, ⟨by intro u v huv; exact huv, hL⟩⟩
  refine ⟨H, hPH.1, ?_, hPH.2, ?_⟩
  · exact WilliamsonShmoys.edgeSet_ncard_mono__p2m_4d05bb9d_42a1_4f6c_b6b4_be7b1a8f6d1e_a1
      (G := L) (H := H) hPH.1
  · intro K hHK hK
    exact WilliamsonShmoys.eq_of_adj_and_edgeSet_ncard_le__p2m_4d05bb9d_42a1_4f6c_b6b4_be7b1a8f6d1e_a1
      (H := H) (K := K) hHK
      (hmax K ⟨(by intro u v huv; exact hHK u v (hPH.1 u v huv)), hK⟩)