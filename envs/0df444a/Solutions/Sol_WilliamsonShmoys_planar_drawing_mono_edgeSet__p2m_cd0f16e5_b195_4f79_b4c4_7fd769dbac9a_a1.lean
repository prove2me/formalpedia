-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_mono_edgeSet__p2m_cd0f16e5_b195_4f79_b4c4_7fd769dbac9a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:59:59.125825+00:00
-- url     : https://prove2.me/submissions/d417393f-deaf-4103-855e-acdb7a782704

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    {A B : SimpleGraph V}
    (hsub : B.edgeSet ⊆ A.edgeSet) :
    WilliamsonShmoys.HasPlanarDrawingOn A →
      WilliamsonShmoys.HasPlanarDrawingOn B := by
  intro hA
  rcases hA with ⟨p, arc, hinj, hedges, hcross⟩
  refine ⟨p, arc, hinj, ?_, ?_⟩
  · intro u v huv hB
    have hmemB : s(u, v) ∈ B.edgeSet := by simpa using hB
    have hmemA : s(u, v) ∈ A.edgeSet := hsub hmemB
    have hAuv : A.Adj u v := by simpa using hmemA
    exact hedges u v huv hAuv
  · intro u v x y huv hxy hB hB' hne t ht s hs heq
    have hmemB : s(u, v) ∈ B.edgeSet := by simpa using hB
    have hmemA : s(u, v) ∈ A.edgeSet := hsub hmemB
    have hAuv : A.Adj u v := by simpa using hmemA
    have hmemB' : s(x, y) ∈ B.edgeSet := by simpa using hB'
    have hmemA' : s(x, y) ∈ A.edgeSet := hsub hmemB'
    have hAxy : A.Adj x y := by simpa using hmemA'
    exact hcross u v x y huv hxy hAuv hAxy hne t ht s hs heq