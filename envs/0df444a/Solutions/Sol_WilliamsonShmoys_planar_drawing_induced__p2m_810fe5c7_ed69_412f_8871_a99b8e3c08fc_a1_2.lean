-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_induced__p2m_810fe5c7_ed69_412f_8871_a99b8e3c08fc_a1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:44:35.080008+00:00
-- url     : https://prove2.me/submissions/f524d54f-54fc-414e-a0fb-484c9a0dcdb3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) (S : Finset V) :
    HasPlanarDrawingOn (G.induce (S : Set V)) := by
  obtain ⟨p, arc, hinj, harc, hcross⟩ := hG
  refine ⟨fun a => p a.1, fun a b => arc a.1 b.1, hinj.comp Subtype.val_injective, ?_, ?_⟩
  · intro u v huv hadj
    obtain ⟨h1, h2, h3, h4, h5⟩ := harc u.1 v.1 huv hadj
    exact ⟨h1, h2, h3, h4, fun t ht w => h5 t ht w.1⟩
  · intro u v x y huv hxy h1 h2 hne t ht s hs heq
    refine hcross u.1 v.1 x.1 y.1 huv hxy h1 h2 ?_ t ht s hs heq
    intro h
    apply hne
    simp only [Prod.mk.injEq] at h ⊢
    exact ⟨Subtype.ext h.1, Subtype.ext h.2⟩
