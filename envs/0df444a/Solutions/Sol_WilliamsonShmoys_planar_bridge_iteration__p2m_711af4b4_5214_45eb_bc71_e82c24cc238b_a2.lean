-- Prove2me | solution 1 for WilliamsonShmoys.planar_bridge_iteration__p2m_711af4b4_5214_45eb_bc71_e82c24cc238b_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:17:02.504187+00:00
-- url     : https://prove2.me/submissions/1ffd98e1-877e-495b-932b-da38bff7eb3d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_finite_graph_extension_connected__p2m_a6ee2644_08f0_4c4d_a139_48d0925fab45_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (bridge : ∀ (G : SimpleGraph V),
      WilliamsonShmoys.HasPlanarDrawingOn G → ¬ G.Connected →
        ∃ u v : V, ¬ G.Reachable u v ∧
          ∃ P : SimpleGraph V,
            (∀ x y : V, P.Adj x y ↔
              G.Adj x y ∨ ((x = u ∧ y = v) ∨ (x = v ∧ y = u))) ∧
            WilliamsonShmoys.HasPlanarDrawingOn P)
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ P : SimpleGraph V,
      N ≤ P ∧ P.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn P := by
  apply WilliamsonShmoys.finite_graph_extension_connected__p2m_a6ee2644_08f0_4c4d_a139_48d0925fab45_a1
    (Good := WilliamsonShmoys.HasPlanarDrawingOn) N hN
  intro G hG hdis
  obtain ⟨u, v, huv, P, hP, hplanar⟩ := bridge G hG hdis
  refine ⟨P, ?_, ?_, hplanar⟩
  · intro x y hxy
    exact (hP x y).2 (Or.inl hxy)
  · intro hEq
    have hPuv : P.Adj u v :=
      (hP u v).2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
    have hGuv : G.Adj u v := hEq ▸ hPuv
    exact huv hGuv.reachable