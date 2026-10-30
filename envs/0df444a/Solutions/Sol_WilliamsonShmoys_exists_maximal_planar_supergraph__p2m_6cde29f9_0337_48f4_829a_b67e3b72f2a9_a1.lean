-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_6cde29f9_0337_48f4_829a_b67e3b72f2a9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:34:11.845006+00:00
-- url     : https://prove2.me/submissions/8f4e471a-2473-4ce4-8be0-1ca49625ca89

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hT : HasPlanarDrawingOn T) :
    ∃ U : SimpleGraph V, T.edgeSet ⊆ U.edgeSet ∧
      HasPlanarDrawingOn U ∧
      ∀ W : SimpleGraph V, U.edgeSet ⊆ W.edgeSet →
        HasPlanarDrawingOn W → U.edgeSet = W.edgeSet := by
  classical
  let P : SimpleGraph V → Prop := fun G => T ≤ G ∧ HasPlanarDrawingOn G
  obtain ⟨U, hdec, hmax⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists P).2 ⟨T, le_rfl, hT⟩
  refine ⟨U, SimpleGraph.edgeSet_subset_edgeSet.mpr hmax.1.1, hmax.1.2, ?_⟩
  intro W hUW hW
  have hUWle : U ≤ W := SimpleGraph.edgeSet_subset_edgeSet.mp hUW
  have hWext : P W := ⟨hmax.1.1.trans hUWle, hW⟩
  have hEq : U = W :=
    (SimpleGraph.IsExtremal.le_iff_eq hmax hWext).mp hUWle
  exact congrArg SimpleGraph.edgeSet hEq