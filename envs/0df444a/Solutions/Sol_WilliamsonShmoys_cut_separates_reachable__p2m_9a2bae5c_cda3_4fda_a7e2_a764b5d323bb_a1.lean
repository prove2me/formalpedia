-- Prove2me | solution 1 for WilliamsonShmoys.cut_separates_reachable__p2m_9a2bae5c_cda3_4fda_a7e2_a764b5d323bb_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:06:18.388661+00:00
-- url     : https://prove2.me/submissions/003e2b7f-6de0-4525-a16f-c43fd3633918

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (S : Set V) (u v : V)
    (hu : u ∈ S) (hv : v ∉ S)
    (hcut : ∀ ⦃a b : V⦄, a ∈ S → b ∉ S → ¬ G.Adj a b) :
    ¬ G.Reachable u v := by
  intro hreach
  have hpath : Relation.ReflTransGen G.Adj u v :=
    (G.reachable_iff_reflTransGen u v).mp hreach
  have hstay : ∀ x, Relation.ReflTransGen G.Adj u x → x ∈ S := by
    intro x hx
    induction hx with
    | refl => exact hu
    | tail _ hadj ih =>
        by_contra hout
        exact (hcut ih hout) hadj
  exact hv (hstay v hpath)