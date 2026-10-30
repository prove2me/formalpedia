-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_6932dd3a_aa87_467b_ad6b_7c92eed114e6_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:17:53.997066+00:00
-- url     : https://prove2.me/submissions/a023af08-d922-4fd0-b816-e4d7e989ddb8

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by
  classical
  let p : SimpleGraph V → Prop := fun H => G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H
  have hp : ∃ H : SimpleGraph V, p H := by
    exact ⟨G, le_rfl, hG⟩
  obtain ⟨H, instH, hExt⟩ := (SimpleGraph.exists_isExtremal_iff_exists (p := p)).2 hp
  letI : DecidableRel H.Adj := instH
  refine ⟨H, hExt.prop.1, hExt.prop.2, ?_⟩
  intro K hHK hK
  have hpK : p K := ⟨hExt.prop.1.trans hHK, hK⟩
  exact (hExt.le_iff_eq hpK).mp hHK |>.symm