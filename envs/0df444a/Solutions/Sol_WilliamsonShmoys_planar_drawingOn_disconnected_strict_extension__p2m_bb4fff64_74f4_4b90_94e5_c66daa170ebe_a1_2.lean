-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawingOn_disconnected_strict_extension__p2m_bb4fff64_74f4_4b90_94e5_c66daa170ebe_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-28T21:54:16.202766+00:00
-- url     : https://prove2.me/submissions/83dc47b8-1f0a-4c44-913e-7d75dee11f80

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
        (M : SimpleGraph V),
        HasPlanarDrawingOn M →
        ¬ M.Connected →
        ∃ N : SimpleGraph V,
          M.edgeSet ⊆ N.edgeSet ∧
          ¬ N.edgeSet ⊆ M.edgeSet ∧
          HasPlanarDrawingOn N) := by
  intro hAll
  letI : Fintype Empty := inferInstance
  letI : LinearOrder Empty := inferInstance
  let M : SimpleGraph Empty := ⊥
  have hDrawing : HasPlanarDrawingOn M := by
    refine ⟨(fun x : Empty => nomatch x), (fun x : Empty => nomatch x), ?_, ?_, ?_⟩
    · intro x
      cases x
    · intro u
      cases u
    · intro u
      cases u
  have hDisconnected : ¬ M.Connected := by
    intro hConn
    rcases hConn.nonempty with ⟨v⟩
    cases v
  obtain ⟨N, hMN, hStrict, hNDrawing⟩ := hAll M hDrawing hDisconnected
  apply hStrict
  have hNM : N ≤ M := by
    intro u v huv
    cases u
  exact (SimpleGraph.edgeSet_subset_edgeSet).mpr hNM