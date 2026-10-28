-- Prove2me | solution 1 for WilliamsonShmoys.local_no_one_edge_extension_implies_global_maximal__p2m_637d5aff_c0b4_44ca_8441_714e49c98d9c_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:26:12.144323+00:00
-- url     : https://prove2.me/submissions/3d0d39d6-8baf-4f3f-a8d9-46854d179494
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_one_edge_planar_intermediate__p2m_87998d71_f36e_4481_bd5e_a0624b01de15_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hNoOneEdgeExtension : ∀ L : SimpleGraph V, K ≤ L →
      L.edgeSet.ncard = K.edgeSet.ncard + 1 →
      WilliamsonShmoys.HasPlanarDrawingOn L → False) :
    ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → K = L := by
  intro L hKL hDrawL
  by_contra hne
  obtain ⟨M, hKM, _hML, hCard, hDrawM⟩ :=
    WilliamsonShmoys.exists_one_edge_planar_intermediate__p2m_87998d71_f36e_4481_bd5e_a0624b01de15_a1
      K L hKL hne hDrawL
  exact hNoOneEdgeExtension M hKM hCard hDrawM