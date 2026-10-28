-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_induced_edge_bound_retry3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T21:26:20.218218+00:00
-- url     : https://prove2.me/submissions/79f015a9-c212-4e5c-afc0-6a4e3d06f50a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_drawing_euler_bound_retry3

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (S : Finset V) (hS : 3 <= S.card)
    (hconn : (H.induce (↑S : Set V)).Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    (H.induce (↑S : Set V)).edgeSet.ncard + 6 <=
      3 * Fintype.card {v // v ∈ S} := by
  rcases hH with ⟨p, arc, hp, hedges, hcross⟩
  have hdraw : WilliamsonShmoys.HasPlanarDrawingOn (H.induce (↑S : Set V)) := by
    refine ⟨(fun v : {v // v ∈ S} => p v.1),
      (fun u v t => arc u.1 v.1 t), ?_, ?_, ?_⟩
    · intro a b hab
      apply Subtype.ext
      exact hp hab
    · intro u v huv hadj
      have h := hedges u.1 v.1 huv hadj
      rcases h with ⟨hc, hi, h0, h1, hint⟩
      refine ⟨hc, hi, h0, h1, ?_⟩
      intro t ht w
      exact hint t ht w.1
    · intro u v x y huv hxy huvAdj hxyAdj hne t ht s hs heq
      have hpair : (u.1, v.1) ≠ (x.1, y.1) := by
        intro h
        apply hne
        have hu : u = x := Subtype.ext (congrArg Prod.fst h)
        have hv : v = y := Subtype.ext (congrArg Prod.snd h)
        rw [hu, hv]
      have hcross' := hcross u.1 v.1 x.1 y.1 huv hxy huvAdj hxyAdj hpair t ht s hs
      exact hcross' heq
  have hcard : 3 <= Fintype.card {v // v ∈ S} := by
    simpa using hS
  exact WilliamsonShmoys.connected_drawing_euler_bound_retry3
    (H.induce (↑S : Set V)) hconn hdraw hcard