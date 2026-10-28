-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_adjoin_cross_component_edge
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T15:34:01.777227+00:00
-- url     : https://prove2.me/submissions/76f2c618-41c8-469a-984f-bc582661f39a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_crossing_free_drawing_add_edge_along_arc
import Theorems.Thm_WilliamsonShmoys_planar_drawing_component_arc

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (u v : V) (huv : u ≠ v)
    (hnot : ¬ Relation.ReflTransGen G.Adj u v) :
    ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.Adj u v := by
  obtain ⟨p, arc, γ, hpinj, hedge, hcross, hγcont, hγinj, hγ0, hγ1,
    hγvert, hγedge⟩ :=
    WilliamsonShmoys.planar_drawing_component_arc G hdraw u v huv hnot
  have hbase :
      Function.Injective p ∧
        (∀ x y, x < y → G.Adj x y →
          ContinuousOn (arc x y) (Set.Icc 0 1) ∧
          Set.InjOn (arc x y) (Set.Icc 0 1) ∧
          arc x y 0 = p x ∧ arc x y 1 = p y ∧
          (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc x y t ≠ p w)) ∧
        (∀ x y a b, x < y → a < b → G.Adj x y → G.Adj a b →
          (x, y) ≠ (a, b) →
          ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            arc x y t = arc a b s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) :=
    ⟨hpinj, hedge, hcross⟩
  exact WilliamsonShmoys.crossing_free_drawing_add_edge_along_arc
    G u v huv p arc hbase γ hγcont hγinj hγ0 hγ1 hγvert hγedge