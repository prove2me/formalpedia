-- Prove2me | solution 1 for WilliamsonShmoys.component_induced_connected_and_planar_drawing_for_component_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T09:59:03.807047+00:00
-- url     : https://prove2.me/submissions/aacd1d53-afd7-4028-a365-aa1cc0c3952d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

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
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (c : M.ConnectedComponent)
    [Fintype {v : V // M.connectedComponentMk v = c}] :
    let S : Type := {v : V // M.connectedComponentMk v = c}
    let H : SimpleGraph S := M.induce (fun v => M.connectedComponentMk v = c)
    H.Connected ∧ HasPlanarDrawingOn H := by
  intro S H
  refine ⟨c.connected_toSimpleGraph, ?_⟩
  exact @S181ind V _ _ M hM (fun v => M.connectedComponentMk v = c)
    (inferInstanceAs (Fintype {v : V // M.connectedComponentMk v = c}))
