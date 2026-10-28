-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_component_support_restrict_4db24ad1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:14:09.521282+00:00
-- url     : https://prove2.me/submissions/28023c39-21c5-4547-a5ed-ce0b6a98684c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn L)
    (C : L.ConnectedComponent)
    [Fintype (↥C.supp)] :
    HasPlanarDrawingOn (L.induce C.supp) := by
  obtain ⟨p, arc, hp, h1, h2⟩ := hdraw
  refine ⟨fun x => p x.1, fun x y => arc x.1 y.1, fun a b h => Subtype.ext (hp h),
    fun u v huv hadj => ?_, fun u v x y huv hxy ha hb hne => ?_⟩
  · obtain ⟨c1, c2, c3, c4, c5⟩ := h1 u.1 v.1 huv hadj
    exact ⟨c1, c2, c3, c4, fun t ht w => c5 t ht w.1⟩
  · refine h2 u.1 v.1 x.1 y.1 huv hxy ha hb ?_
    intro h
    apply hne
    simp only [Prod.mk.injEq] at h ⊢
    exact ⟨Subtype.ext h.1, Subtype.ext h.2⟩
