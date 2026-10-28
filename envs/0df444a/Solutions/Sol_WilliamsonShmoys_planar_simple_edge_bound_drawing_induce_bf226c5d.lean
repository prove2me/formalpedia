-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_edge_bound_drawing_induce_bf226c5d
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:42:19.39787+00:00
-- url     : https://prove2.me/submissions/4712d954-e66f-4ff4-8fee-53b57b8f0578

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

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
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (S : Set V) [Fintype S] :
    WilliamsonShmoys.HasPlanarDrawingOn (G.induce S) := by
  exact S181ind G hG S
