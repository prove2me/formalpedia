-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_induce__p2m_23ef3f28_c786_4f0c_b412_311d85f11230_a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:24:33.793653+00:00
-- url     : https://prove2.me/submissions/4fa5b4e3-390d-4497-8d70-cfaaa432558e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (W : Set V)
    [Fintype {v : V // v ∈ W}] :
    WilliamsonShmoys.HasPlanarDrawingOn (H.induce W) := by
  obtain ⟨p, arc, hp, h1, h2⟩ := hH
  refine ⟨fun v => p v.1, fun u v => arc u.1 v.1, hp.comp Subtype.val_injective, ?_, ?_⟩
  · intro u v huv hadj
    obtain ⟨c1, c2, c3, c4, c5⟩ := h1 u.1 v.1 huv hadj
    exact ⟨c1, c2, c3, c4, fun t ht w => c5 t ht w.1⟩
  · intro u v x y huv hxy ha hb hne t ht s hs heq
    refine h2 u.1 v.1 x.1 y.1 huv hxy ha hb ?_ t ht s hs heq
    intro h
    apply hne
    simp only [Prod.mk.injEq] at h ⊢
    exact ⟨Subtype.ext h.1, Subtype.ext h.2⟩
