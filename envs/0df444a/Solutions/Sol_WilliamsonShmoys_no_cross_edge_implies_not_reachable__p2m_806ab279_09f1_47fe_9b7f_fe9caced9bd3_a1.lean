-- Prove2me | solution 1 for WilliamsonShmoys.no_cross_edge_implies_not_reachable__p2m_806ab279_09f1_47fe_9b7f_fe9caced9bd3_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:34:54.136034+00:00
-- url     : https://prove2.me/submissions/a925343c-e1ce-4c80-9f4c-e479eee511a3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (A : Set V)
    (hno : ∀ u ∈ A, ∀ v ∉ A, ¬ G.Adj u v)
    (u v : V) (hu : u ∈ A) (hv : v ∉ A) :
    ¬ G.Reachable u v := by
  intro hreach
  have hclosed : ∀ {x y : V}, G.Walk x y → x ∈ A → y ∈ A := by
    intro x y w hx
    induction w with
    | nil => exact hx
    | @cons x z y hadj w ih =>
        apply ih
        by_contra hz
        exact hno x hx z hz hadj
  exact hv (hreach.elim fun w => hclosed w hu)