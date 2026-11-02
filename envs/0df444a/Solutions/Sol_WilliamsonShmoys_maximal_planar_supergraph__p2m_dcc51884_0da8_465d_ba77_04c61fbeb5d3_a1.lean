-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph__p2m_dcc51884_0da8_465d_ba77_04c61fbeb5d3_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:54:50.909478+00:00
-- url     : https://prove2.me/submissions/2d079d73-7d39-4551-9dd3-2e8154f18005

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hT : HasPlanarDrawingOn T) :
    ∃ U : SimpleGraph V,
      T ≤ U ∧ HasPlanarDrawingOn U ∧
        ∀ H : SimpleGraph V, U ≤ H → HasPlanarDrawingOn H → H ≤ U := by
  classical
  let p : SimpleGraph V → Prop := fun U => T ≤ U ∧ HasPlanarDrawingOn U
  obtain ⟨U, hTU, hmax⟩ :=
    Finite.exists_le_maximal (a := T) (p := p) (show p T from ⟨le_rfl, hT⟩)
  refine ⟨U, hTU, hmax.1.2, ?_⟩
  intro H hUH hH
  have hpH : p H := ⟨hTU.trans hUH, hH⟩
  exact hmax.2 hpH hUH