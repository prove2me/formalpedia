-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_db2bc25d_3c02_46be_91b6_cd4d6f11e2cd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T19:51:52.111237+00:00
-- url     : https://prove2.me/submissions/5fe24725-457b-4d11-b0ce-7cef68e65de2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
    ∃ R : SimpleGraph V, G ≤ R ∧ HasPlanarDrawingOn R ∧
      ∀ H : SimpleGraph V, R ≤ H → HasPlanarDrawingOn H → H = R := by
  classical
  let P : SimpleGraph V → Prop := fun X => G ≤ X ∧ HasPlanarDrawingOn X
  obtain ⟨R, hDecR, hMax⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists (p := P)).2 ⟨G, le_rfl, hG⟩
  letI : DecidableRel R.Adj := hDecR
  refine ⟨R, hMax.prop.1, hMax.prop.2, ?_⟩
  intro H hRH hH
  have hDecH : DecidableRel H.Adj := Classical.decRel _
  letI : DecidableRel H.Adj := hDecH
  have hCandidate : P H := ⟨le_trans hMax.prop.1 hRH, hH⟩
  have hEq : R = H :=
    (SimpleGraph.IsExtremal.le_iff_eq hMax hCandidate).mp hRH
  exact hEq.symm
