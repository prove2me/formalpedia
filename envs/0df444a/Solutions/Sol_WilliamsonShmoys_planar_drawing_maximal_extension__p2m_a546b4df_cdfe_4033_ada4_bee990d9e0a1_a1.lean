-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_a546b4df_cdfe_4033_ada4_bee990d9e0a1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:14:01.551438+00:00
-- url     : https://prove2.me/submissions/43ada807-2925-44e4-9dfb-b29978559282

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V) (hDraw : HasPlanarDrawingOn R)
    (hV : 3 <= Fintype.card V) :
    ∃ S : SimpleGraph V, R ≤ S ∧ HasPlanarDrawingOn S ∧
      ∀ T : SimpleGraph V, S ≤ T → HasPlanarDrawingOn T → T = S := by
  classical
  let p : SimpleGraph V → Prop := fun S => R ≤ S ∧ HasPlanarDrawingOn S
  have hseed : p R := ⟨le_rfl, hDraw⟩
  obtain ⟨S, hRS, hmax⟩ := Finite.exists_le_maximal (p := p) hseed
  refine ⟨S, hRS, hmax.1.2, ?_⟩
  intro T hST hT
  exact le_antisymm (hmax.2 ⟨hRS.trans hST, hT⟩ hST) hST