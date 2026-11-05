-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_a5f3545b_9213_4099_bf3a_a8a2e64023e0_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T20:23:04.729051+00:00
-- url     : https://prove2.me/submissions/23a27076-8b0c-437a-acb6-3212756f3bb9

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option linter.unusedVariables false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hV : LE.le 3 (Fintype.card V))
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) :
    ∃ T' : SimpleGraph V,
      LE.le T T' ∧ WilliamsonShmoys.HasPlanarDrawingOn T' ∧
      ∀ U : SimpleGraph V,
        LE.le T' U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T' := by
  classical
  let p : SimpleGraph V → Prop :=
    fun T' => T ≤ T' ∧ WilliamsonShmoys.HasPlanarDrawingOn T'
  have hpT : p T := ⟨le_rfl, hT⟩
  obtain ⟨T', _hTT', hmax⟩ :=
    (Finite.exists_le_maximal (α := SimpleGraph V) (p := p) (a := T) hpT)
  rcases hmax with ⟨hpT', hmax'⟩
  refine ⟨T', hpT'.1, hpT'.2, ?_⟩
  intro U hTU hU
  have hUT : U ≤ T' := hmax' ⟨hpT'.1.trans hTU, hU⟩ hTU
  exact (le_antisymm hTU hUT).symm
