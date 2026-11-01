-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_add_edge_across_separation__p2m_3eced331_e15d_452f_ac43_a684696313f5_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:15:43.357145+00:00
-- url     : https://prove2.me/submissions/d979e91b-e916-4bba-ab93-716cd987a013
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_between_components__p2m_726a076b_6e45_45f6_9bfc_717031618dd6_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (u v : V) (A : Set V)
    (huA : u ∈ A) (hvA : v ∉ A)
    (hsep : ∀ a b, a ∈ A → b ∉ A → ¬ G.Adj a b) :
    ∃ H : SimpleGraph V,
      (∀ a b, H.Adj a b ↔
        G.Adj a b ∨ ((a = u ∧ b = v) ∨ (a = v ∧ b = u))) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by
  apply WilliamsonShmoys.planar_drawing_add_edge_between_components__p2m_726a076b_6e45_45f6_9bfc_717031618dd6_a1 G hG u v
  intro huv
  have hwalk : ∀ {x y : V}, G.Walk x y → x ∈ A → y ∈ A := by
    intro x y p
    induction p with
    | nil =>
        intro hx
        exact hx
    | @cons x y z hadj p ih =>
        intro hx
        have hy : y ∈ A := by
          by_contra hy
          exact (hsep x y hx hy) hadj
        exact ih hy
  have hvA' : v ∈ A := huv.elim fun p => hwalk p huA
  exact hvA hvA'