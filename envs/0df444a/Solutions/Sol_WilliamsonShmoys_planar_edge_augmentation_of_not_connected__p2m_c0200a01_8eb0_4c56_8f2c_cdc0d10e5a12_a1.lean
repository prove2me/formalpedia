-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_augmentation_of_not_connected__p2m_c0200a01_8eb0_4c56_8f2c_cdc0d10e5a12_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:51:00.645495+00:00
-- url     : https://prove2.me/submissions/5296e423-1f8f-4810-bdb4-bd286ad81db4

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_connected
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_planar_edge_extension_of_disconnected_drawing
import Theorems.Thm_WilliamsonShmoys_planar_drawing_extension_for_edge_bound_ef555edc

set_option autoImplicit false
open WilliamsonShmoys
open scoped BigOperators

theorem solution {V : Type} [Fintype V] [LinearOrder V] (U : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hU : HasPlanarDrawingOn U) (hdisc : ¬ U.Connected) : ∃ (a b : V) (W : SimpleGraph V), a ≠ b ∧ ¬ U.Adj a b ∧ U ≤ W ∧ W ≠ U ∧ W.Adj a b ∧ HasPlanarDrawingOn W := by
  obtain ⟨J, hUJ, hne, hJ⟩ := WilliamsonShmoys.planar_edge_extension_of_disconnected_drawing U hU hV hdisc
  obtain ⟨a, b, hJab, hUab⟩ : ∃ a b, J.Adj a b ∧ ¬ U.Adj a b := by
    by_contra hc
    push_neg at hc
    exact hne (le_antisymm (fun x y h => hc x y h) hUJ)
  exact ⟨a, b, J, hJab.ne, hUab, hUJ, hne, hJab, hJ⟩
