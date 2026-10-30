-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_connected_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T00:27:54.388871+00:00
-- url     : https://prove2.me/submissions/9e2eb050-f6a7-4443-9cb8-c08a92951115

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_97829890_428d_4657_a899_f7e200a68a7c_a4
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_is_connected__p2m_97829890_428d_4657_a899_f7e200a68a7c_a4

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ K.Connected ∧ HasPlanarDrawingOn K := by
  obtain ⟨K, hHK, hK, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_97829890_428d_4657_a899_f7e200a68a7c_a4 H hH
  exact ⟨K, hHK,
    WilliamsonShmoys.maximal_planar_drawing_is_connected__p2m_97829890_428d_4657_a899_f7e200a68a7c_a4 K hK hCard hMax,
    hK⟩