-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_e23427be_8e8a_4c77_a28e_0966a53f4506_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:13:12.202998+00:00
-- url     : https://prove2.me/submissions/769df2ea-82ae-45a3-b602-04b676b78745
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_2368bce9_0700_4bbd_ab4b_7c13a596af1d_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hHmax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hKplanar, hKE⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_2368bce9_0700_4bbd_ab4b_7c13a596af1d_a1
      H hV hH
  have hKH : K ≤ H := hHmax K hHK hKplanar
  have hEq : H = K := le_antisymm hHK hKH
  rw [← hEq] at hKE
  exact hKE