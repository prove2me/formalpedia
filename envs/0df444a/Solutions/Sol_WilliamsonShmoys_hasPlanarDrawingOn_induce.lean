-- Prove2me | solution 1 for WilliamsonShmoys.hasPlanarDrawingOn_induce
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T09:19:00.960522+00:00
-- url     : https://prove2.me/submissions/6b66b6b2-53b4-403b-9540-a4caa2233a31

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem S181ind {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (S : Set V) [Fintype S] :
    WilliamsonShmoys.HasPlanarDrawingOn (H.induce S) := by
  obtain ⟨p, arc, hp, h1, h2⟩ := hH
  refine ⟨fun x => p x.1, fun x y => arc x.1 y.1, fun x y h => Subtype.ext (hp h),
    fun u v huv hadj => ?_, fun u v x y huv hxy h3 h4 hne => ?_⟩
  · obtain ⟨a, b, c, d, e⟩ := h1 u.1 v.1 huv hadj
    exact ⟨a, b, c, d, fun t ht w => e t ht w.1⟩
  · refine h2 u.1 v.1 x.1 y.1 huv hxy h3 h4 ?_
    intro h
    apply hne
    simp only [Prod.mk.injEq] at h ⊢
    exact ⟨Subtype.ext h.1, Subtype.ext h.2⟩


theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (S : Set V) [Fintype S] :
    WilliamsonShmoys.HasPlanarDrawingOn (K.induce S) := by
  exact S181ind K hK S
