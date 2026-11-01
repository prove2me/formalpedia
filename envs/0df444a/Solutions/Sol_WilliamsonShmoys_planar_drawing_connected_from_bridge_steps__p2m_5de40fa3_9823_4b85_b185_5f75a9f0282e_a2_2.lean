-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_connected_from_bridge_steps__p2m_5de40fa3_9823_4b85_b185_5f75a9f0282e_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:49:40.959311+00:00
-- url     : https://prove2.me/submissions/2ab6f269-4748-48f5-b55f-460018b7e146

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_finite_graph_bridge_extension_connected__p2m_be2db1e0_df49_4de2_8924_46bf2933b6cf_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V)
    (hbridge : ∀ (G : SimpleGraph V), HasPlanarDrawingOn G →
      ∀ (A : Set V), A.Nonempty → Aᶜ.Nonempty →
        (∀ u ∈ A, ∀ v ∉ A, ¬ G.Adj u v) →
        ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
          ∃ u v, u ∈ A ∧ v ∉ A ∧ H.Adj u v) :
    ∃ H : SimpleGraph V, K ≤ H ∧ HasPlanarDrawingOn H ∧ H.Connected := by
  exact finite_graph_bridge_extension_connected__p2m_be2db1e0_df49_4de2_8924_46bf2933b6cf_a2
    (P := HasPlanarDrawingOn) K hK (by omega) hbridge