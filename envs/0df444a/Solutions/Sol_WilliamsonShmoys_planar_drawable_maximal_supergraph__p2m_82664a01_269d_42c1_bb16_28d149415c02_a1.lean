-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawable_maximal_supergraph__p2m_82664a01_269d_42c1_bb16_28d149415c02_a1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:42:29.388309+00:00
-- url     : https://prove2.me/submissions/e7247ae8-bb3e-4c25-9a77-f8a81fd21d36

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R) :
    ∃ T : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn T ∧
      R ≤ T ∧
      ∀ U : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn U → T ≤ U → U = T := by
  obtain ⟨T, -, hT⟩ := Finite.exists_le_maximal
    (p := fun S : SimpleGraph V => R ≤ S ∧ HasPlanarDrawingOn S) (a := R) ⟨le_rfl, hR⟩
  refine ⟨T, hT.1.2, hT.1.1, fun U hU h1 => ?_⟩
  exact le_antisymm (hT.2 ⟨hT.1.1.trans h1, hU⟩ h1) h1
