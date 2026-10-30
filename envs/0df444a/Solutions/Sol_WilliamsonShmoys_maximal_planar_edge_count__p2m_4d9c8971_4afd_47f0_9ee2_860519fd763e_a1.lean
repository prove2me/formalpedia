-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_4d9c8971_4afd_47f0_9ee2_860519fd763e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T22:41:06.774604+00:00
-- url     : https://prove2.me/submissions/14f8102f-93d8-4c0e-9650-b6610e03b2e2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension__p2m_ef21e4d0_72a9_49ba_9f8c_1146d558edeb_a7

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hCard : 3 <= Fintype.card V)
    (hT : HasPlanarDrawingOn T)
    (hMax : ∀ u v, u ≠ v → ¬ T.Adj u v →
      ¬ ∃ U : SimpleGraph V,
        (∀ x y, T.Adj x y → U.Adj x y) ∧
        HasPlanarDrawingOn U ∧ U.Adj u v) :
    T.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨U, hTU, hU, hCount⟩ :=
    WilliamsonShmoys.maximal_planar_extension__p2m_ef21e4d0_72a9_49ba_9f8c_1146d558edeb_a7
      T hCard hT
  have hEq : U = T := by
    ext x y
    constructor
    · intro hxy
      by_cases hTxy : T.Adj x y
      · exact hTxy
      · exact False.elim (hMax x y hxy.ne hTxy ⟨U, hTU, hU, hxy⟩)
    · exact hTU x y
  rw [hEq] at hCount
  exact hCount