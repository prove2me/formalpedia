-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_component_cut__p2m_bde12a09_c3ff_49b5_827a_2421e10fc278_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:08:46.61463+00:00
-- url     : https://prove2.me/submissions/ebcf2f95-5266-4bc2-a30e-1b0b44e0ae5e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_component_cut_edges__p2m_19cd2d46_2b88_4ae0_bdf6_b262bd78d159_a1
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_mono__p2m_19cd2d46_2b88_4ae0_bdf6_b262bd78d159_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) (u v : V)
    (hdisj : ¬ G.Reachable u v) :
    ∃ S : Set V, ∃ A B : SimpleGraph V,
      u ∈ S ∧ v ∉ S ∧
      (∀ a b, G.Adj a b ↔ A.Adj a b ∨ B.Adj a b) ∧
      (∀ a b, A.Adj a b → a ∈ S ∧ b ∈ S) ∧
      (∀ a b, B.Adj a b → a ∉ S ∧ b ∉ S) ∧
      HasPlanarDrawingOn A ∧ HasPlanarDrawingOn B := by
  obtain ⟨S, A, B, hu, hv, hpartition, hA, hB⟩ :=
    WilliamsonShmoys.component_cut_edges__p2m_19cd2d46_2b88_4ae0_bdf6_b262bd78d159_a1 G u v hdisj
  exact ⟨S, A, B, hu, hv, hpartition, hA, hB,
    WilliamsonShmoys.planarDrawingOn_mono__p2m_19cd2d46_2b88_4ae0_bdf6_b262bd78d159_a1 G A hG
      (fun a b hab => (hpartition a b).mpr (Or.inl hab)),
    WilliamsonShmoys.planarDrawingOn_mono__p2m_19cd2d46_2b88_4ae0_bdf6_b262bd78d159_a1 G B hG
      (fun a b hab => (hpartition a b).mpr (Or.inr hab))⟩