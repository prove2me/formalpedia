-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_f0debea5_402c_48d1_9751_ec911f78abab_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:44:49.67844+00:00
-- url     : https://prove2.me/submissions/d3c100df-afc4-4da6-ba0b-307a9e996db6

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_triangulation__p2m_4eb14725_e37b_413a_b3b4_00357af41eb8_a1__p2m_4eb14725_e37b_413a_b3b4_00357af41eb8_a4

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) [DecidableRel N.Adj]
    (hcard : 3 ≤ Fintype.card V) (hN : HasPlanarDrawingOn N)
    (hmax : ∀ (P : SimpleGraph V) [DecidableRel P.Adj],
      N ≤ P → HasPlanarDrawingOn P → P = N) :
    N.edgeFinset.card + 6 = 3 * Fintype.card V := by
  classical
  obtain ⟨P, hle, hP, hcount⟩ :=
    WilliamsonShmoys.maximal_drawable_graph_has_triangulation__p2m_4eb14725_e37b_413a_b3b4_00357af41eb8_a1__p2m_4eb14725_e37b_413a_b3b4_00357af41eb8_a4
      N hcard hN
  have hPN : P = N := hmax P hle hP
  cases hPN
  exact hcount
