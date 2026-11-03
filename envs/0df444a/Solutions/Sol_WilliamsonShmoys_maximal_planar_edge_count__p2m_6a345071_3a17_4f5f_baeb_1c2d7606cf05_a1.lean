-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_6a345071_3a17_4f5f_baeb_1c2d7606cf05_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:17:08.867195+00:00
-- url     : https://prove2.me/submissions/a6809843-4229-4630-b4ad-c3e4dd7b8d7c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_exact_edge_count__p2m_d140b1f8_6ceb_482c_820e_597e29c34ec2_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ H : SimpleGraph V, K ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨H, hKH, hH, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension_exact_edge_count__p2m_d140b1f8_6ceb_482c_820e_597e29c34ec2_a1 K hcard hK
  have hHK : H ≤ K := hmax H hKH hH
  have hEq : K = H := le_antisymm hKH hHK
  rw [hEq]
  exact hcount