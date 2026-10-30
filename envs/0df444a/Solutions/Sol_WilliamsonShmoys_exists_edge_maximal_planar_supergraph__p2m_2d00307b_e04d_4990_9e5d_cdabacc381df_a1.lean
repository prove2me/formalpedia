-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_2d00307b_e04d_4990_9e5d_cdabacc381df_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:38:44.729204+00:00
-- url     : https://prove2.me/submissions/e1c87e29-0df0-48a9-b6ac-7925778d3647

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by
  classical
  let p : SimpleGraph V → Prop := fun X => G ≤ X ∧ WilliamsonShmoys.HasPlanarDrawingOn X
  obtain ⟨H, hDec, hExt⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists p).2 ⟨G, le_rfl, hplanar⟩
  letI : DecidableRel H.Adj := hDec
  refine ⟨H, hExt.prop.1, hExt.prop.2, ?_⟩
  intro K hHK hK
  have hKp : p K := ⟨hExt.prop.1.trans hHK, hK⟩
  have hEq : H = K := (hExt.le_iff_eq hKp).1 hHK
  exact hEq.symm