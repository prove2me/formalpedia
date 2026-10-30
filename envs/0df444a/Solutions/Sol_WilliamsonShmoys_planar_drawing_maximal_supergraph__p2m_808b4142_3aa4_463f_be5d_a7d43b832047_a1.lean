-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_808b4142_3aa4_463f_be5d_a7d43b832047_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:25:25.509022+00:00
-- url     : https://prove2.me/submissions/e0421ab3-162a-4cfc-9183-2835138194ef

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, K ≤ H ∧ HasPlanarDrawingOn H ∧
      ∀ L : SimpleGraph V, H ≤ L → HasPlanarDrawingOn L → L = H := by
  classical
  let S : Set (SimpleGraph V) := {G | K ≤ G ∧ HasPlanarDrawingOn G}
  have hS_nonempty : S.Nonempty := ⟨K, le_rfl, hK⟩
  obtain ⟨H, hHmax⟩ := (Set.toFinite S).exists_maximal hS_nonempty
  refine ⟨H, hHmax.1.1, hHmax.1.2, ?_⟩
  intro L hHL hL
  have hLS : L ∈ S := ⟨le_trans hHmax.1.1 hHL, hL⟩
  exact le_antisymm (hHmax.2 hLS hHL) hHL