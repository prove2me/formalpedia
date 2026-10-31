-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_extension__p2m_ddfe16f2_466b_4eda_98ed_20e5107df448_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:33:44.218502+00:00
-- url     : https://prove2.me/submissions/18aa8bd9-45e7-4901-bf06-87bb6fd724ad

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Order.Preorder.Finite

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V) (hDraw : HasPlanarDrawingOn R) :
    ∃ T : SimpleGraph V, R ≤ T ∧ HasPlanarDrawingOn T ∧
      ∀ N : SimpleGraph V, T ≤ N → HasPlanarDrawingOn N → N ≤ T := by
  classical
  let P : SimpleGraph V → Prop := fun G => R ≤ G ∧ HasPlanarDrawingOn G
  have hfinite : {G : SimpleGraph V | P G}.Finite := Set.toFinite _
  have hR : R ∈ {G : SimpleGraph V | P G} := ⟨le_rfl, hDraw⟩
  obtain ⟨T, hRT, hmax⟩ := Set.Finite.exists_le_maximal hfinite hR
  refine ⟨T, hRT, hmax.1.2, ?_⟩
  intro N hTN hN
  have hNP : N ∈ {G : SimpleGraph V | P G} := ⟨hRT.trans hTN, hN⟩
  exact hmax.2 hNP hTN