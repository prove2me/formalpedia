-- Prove2me | solution 2 for WilliamsonShmoys.component_planar_drawing__p2m_16ddb684_8eab_45f4_881b_4391d956c1ce_a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T07:46:56.421661+00:00
-- url     : https://prove2.me/submissions/35effe83-a4c9-454c-9784-0be9bace498d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (C : L.ConnectedComponent)
    [Fintype C.supp] :
    WilliamsonShmoys.HasPlanarDrawingOn C.toSimpleGraph := by
  obtain ⟨p, arc, hp, h1, h2⟩ := hL
  refine ⟨fun u => p u.val, fun u v => arc u.val v.val, hp.comp Subtype.val_injective, ?_, ?_⟩
  · intro u v huv hA
    obtain ⟨c1, c2, c3, c4, c5⟩ := h1 u.val v.val huv hA
    exact ⟨c1, c2, c3, c4, fun t ht w => c5 t ht w.val⟩
  · intro u v x y huv hxy hA hB hne
    exact h2 u.val v.val x.val y.val huv hxy hA hB (fun h => hne (by
      simp only [Prod.mk.injEq] at h ⊢
      exact ⟨Subtype.ext h.1, Subtype.ext h.2⟩))
