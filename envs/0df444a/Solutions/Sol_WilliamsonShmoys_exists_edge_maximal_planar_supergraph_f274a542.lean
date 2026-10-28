-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_maximal_planar_supergraph_f274a542
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:26:15.599299+00:00
-- url     : https://prove2.me/submissions/573e1979-428c-4533-b040-48a293ad393b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_nonempty_predicate_has_maximal

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V,
        L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by
  classical
  let P : SimpleGraph V → Prop := fun L =>
    K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L
  obtain ⟨L, hL, hmax⟩ := finite_nonempty_predicate_has_maximal
    (α := SimpleGraph V) P ⟨K, le_rfl, hK⟩
  refine ⟨L, hL.1, hL.2, ?_⟩
  intro M hLM hM
  have hPM : P M := ⟨hL.1.trans hLM, hM⟩
  have hML : M ≤ L := hmax M hPM hLM
  exact le_antisymm hML hLM