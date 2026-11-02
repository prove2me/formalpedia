-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_extends_to_edge_maximal__p2m_a40304d1_03ef_470a_a877_21a5de02f724_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:58:15.05495+00:00
-- url     : https://prove2.me/submissions/09d7cbbc-b5a7-42bf-8df1-b9256e4c3a07

import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_maximal__p2m_827ca239_4f02_4972_bc30_3603c6ba3647_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) [DecidableRel L.Adj]
    (hL : HasPlanarDrawingOn L) (hcard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, ∃ (dH : DecidableRel H.Adj),
      (letI : DecidableRel H.Adj := dH;
        L.edgeFinset ⊆ H.edgeFinset ∧ HasPlanarDrawingOn H ∧
          (∀ K : SimpleGraph V,
            (∀ u v, H.Adj u v → K.Adj u v) → HasPlanarDrawingOn K →
              ∀ u v, K.Adj u v → H.Adj u v)) := by
  classical
  obtain ⟨H, dH, hH⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_maximal__p2m_827ca239_4f02_4972_bc30_3603c6ba3647_a1
      L HasPlanarDrawingOn hL
  exact ⟨H, dH, hH⟩