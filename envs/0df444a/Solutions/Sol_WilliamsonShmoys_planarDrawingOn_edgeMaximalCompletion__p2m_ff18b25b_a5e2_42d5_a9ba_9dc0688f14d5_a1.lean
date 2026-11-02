-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_edgeMaximalCompletion__p2m_ff18b25b_a5e2_42d5_a9ba_9dc0688f14d5_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:38:18.559781+00:00
-- url     : https://prove2.me/submissions/f4ac77b1-aed6-4290-9203-281d1d7c1094

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K) :
    ∃ K' : SimpleGraph V, K ≤ K' ∧ HasPlanarDrawingOn K' ∧
      ∀ H : SimpleGraph V, K' ≤ H → HasPlanarDrawingOn H → H = K' := by
  classical
  let admissible : SimpleGraph V → Prop := fun G => K ≤ G ∧ HasPlanarDrawingOn G
  have hex : ∃ G : SimpleGraph V, admissible G := ⟨K, le_rfl, hK⟩
  obtain ⟨K', _, hmax⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists (p := admissible)).2 hex
  refine ⟨K', hmax.prop.1, hmax.prop.2, ?_⟩
  intro H hKH hH
  have hAdmissible : admissible H := ⟨hmax.prop.1.trans hKH, hH⟩
  exact ((hmax.le_iff_eq hAdmissible).mp hKH).symm