-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_augment_sparse_planar_graph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T01:32:16.484207+00:00
-- url     : https://prove2.me/submissions/9ea0d374-df51-4543-b371-d08a24b60ba3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_planar_drawing_on_maximal_supergraph
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_on_euler_edge_bound

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : HasPlanarDrawingOn T)
    (hCard : 3 ≤ Fintype.card V)
    (hSparse : T.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ U : SimpleGraph V, HasPlanarDrawingOn U ∧
      (∀ u v, T.Adj u v → U.Adj u v) ∧
      ∃ u v, ¬ T.Adj u v ∧ U.Adj u v := by
  obtain ⟨U, hU, hTU, hMax⟩ :=
    WilliamsonShmoys.finite_planar_drawing_on_maximal_supergraph T hT
  have hBound :=
    WilliamsonShmoys.maximal_planar_drawing_on_euler_edge_bound U hU hCard hMax
  have hNe : U ≠ T := by
    intro hEq
    subst U
    omega
  have hNew : ∃ u v, ¬ T.Adj u v ∧ U.Adj u v := by
    by_contra hn
    have hUT : ∀ u v, U.Adj u v → T.Adj u v := by
      intro u v huv
      by_contra hnot
      exact hn ⟨u, v, hnot, huv⟩
    have hEq : U = T := by
      ext u v
      exact ⟨fun huv => hUT u v huv, fun huv => hTU u v huv⟩
    exact hNe hEq
  exact ⟨U, hU, hTU, hNew⟩