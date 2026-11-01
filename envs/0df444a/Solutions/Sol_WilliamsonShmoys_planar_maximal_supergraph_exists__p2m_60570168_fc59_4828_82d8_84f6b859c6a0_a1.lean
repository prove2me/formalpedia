-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_supergraph_exists__p2m_60570168_fc59_4828_82d8_84f6b859c6a0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:05:32.223433+00:00
-- url     : https://prove2.me/submissions/8c7aeda0-d41e-47a3-9ac3-13f021f2f13c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L) :
    ∃ K : SimpleGraph V,
      L ≤ K ∧ HasPlanarDrawingOn K ∧
        ∀ M : SimpleGraph V, K ≤ M → HasPlanarDrawingOn M → M ≤ K := by
  classical
  let p : SimpleGraph V → Prop := fun G => L ≤ G ∧ HasPlanarDrawingOn G
  obtain ⟨K, hdecK, hKext⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists (V := V) p).2 ⟨L, le_rfl, hL⟩
  letI : DecidableRel K.Adj := hdecK
  refine ⟨K, hKext.1.1, hKext.1.2, ?_⟩
  intro M hKM hM
  have hMp : p M := ⟨le_trans hKext.1.1 hKM, hM⟩
  have hEq : K = M :=
    (SimpleGraph.IsExtremal.le_iff_eq hKext hMp).mp hKM
  simpa [hEq]