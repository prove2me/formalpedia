-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_edge_maximal_completion__p2m_7cf6806e_5be6_4790_8cad_719b856f9dab_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:16:55.081546+00:00
-- url     : https://prove2.me/submissions/5472d6f9-31aa-417f-b723-376c0dc5f93a

import Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_drawable_extension__p2m_aebf59bd_f6b5_46a8_a852_f6c4896d39c8_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) : ∃ K : SimpleGraph V, (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ (∀ L : SimpleGraph V, (∀ ⦃u v : V⦄, K.Adj u v → L.Adj u v) → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :=
  WilliamsonShmoys.planar_supergraph_maximal_drawable_extension__p2m_aebf59bd_f6b5_46a8_a852_f6c4896d39c8_a1 H hH hV
