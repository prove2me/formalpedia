-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_has_triangulated_face_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T17:56:19.757031+00:00
-- url     : https://prove2.me/submissions/f3c097bd-8739-4c97-9ad4-bbf67c93e450
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_for_face_count_85360098_dba7_4c11_ba84_e51ff8660a8a

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hmax : ∀ T : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn T →
      R ≤ T → T = R)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = R.edgeSet.ncard + 2 ∧
      3 * f = 2 * R.edgeSet.ncard := by
  have he := WilliamsonShmoys.maximal_drawable_graph_edge_count_for_face_count_85360098_dba7_4c11_ba84_e51ff8660a8a
    R hR hmax hCard
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega