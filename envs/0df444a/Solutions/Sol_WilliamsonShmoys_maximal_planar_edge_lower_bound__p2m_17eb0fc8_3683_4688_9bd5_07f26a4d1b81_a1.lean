-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_17eb0fc8_3683_4688_9bd5_07f26a4d1b81_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:34:11.660542+00:00
-- url     : https://prove2.me/submissions/d6e9f639-c926-4246-ba80-d3bda2b7aaa2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_triangulation_extension__p2m_e98f9a30_577d_4730_aed3_8f09e7d6352a_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hK : HasPlanarDrawingOn K)
    (hmax : ∀ H : SimpleGraph V, K ≤ H → HasPlanarDrawingOn H → H ≤ K) :
    3 * (Fintype.card V - 2) ≤ K.edgeSet.ncard := by
  obtain ⟨H, hKH, hH, hbound⟩ :=
    WilliamsonShmoys.drawable_triangulation_extension__p2m_e98f9a30_577d_4730_aed3_8f09e7d6352a_a1
      K hV hK
  have hHK : H ≤ K := hmax H hKH hH
  have heq : H = K := le_antisymm hHK hKH
  simpa [heq] using hbound
