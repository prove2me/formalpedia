-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_6ab13955_ca33_41a0_b892_672767e48ad0_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T18:44:25.005468+00:00
-- url     : https://prove2.me/submissions/e2bbf476-ff75-45c9-901f-43c2bfe61eac

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V) (hDraw : HasPlanarDrawingOn Q) :
    ∃ R : SimpleGraph V, Q ≤ R ∧ HasPlanarDrawingOn R ∧
      (∀ S : SimpleGraph V, R ≤ S → HasPlanarDrawingOn S → S = R) := by
  classical
  let p : SimpleGraph V → Prop := fun R => Q ≤ R ∧ HasPlanarDrawingOn R
  have hpQ : p Q := ⟨le_rfl, hDraw⟩
  obtain ⟨R, _hQR, hmax⟩ :=
    (Finite.exists_le_maximal (α := SimpleGraph V) (p := p) (a := Q) hpQ)
  rcases hmax with ⟨hpR, hmax'⟩
  refine ⟨R, hpR.1, hpR.2, ?_⟩
  intro S hRS hS
  have hpS : p S := ⟨hpR.1.trans hRS, hS⟩
  exact (le_antisymm hRS (hmax' hpS hRS)).symm
