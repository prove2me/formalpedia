-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_878ddd3e_03fb_448c_a8d8_103ff049e818_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:19:40.827597+00:00
-- url     : https://prove2.me/submissions/0411d89a-65da-45f2-8ffe-d8d861e4a39c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard ∧
      (∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K) := by
  classical
  let S : Set (SimpleGraph V) := {K | H ≤ K ∧ HasPlanarDrawingOn K}
  have hSne : S.Nonempty := ⟨H, le_rfl, hH⟩
  obtain ⟨K, hK, hKmax⟩ := (Set.toFinite S).exists_maximal hSne
  change H ≤ K ∧ HasPlanarDrawingOn K at hK
  refine ⟨K, hK.1, hK.2, ?_, ?_⟩
  · exact Set.ncard_mono (SimpleGraph.edgeSet_mono hK.1)
  · intro L hKL hL
    exact hKmax ⟨hK.1.trans hKL, hL⟩ hKL