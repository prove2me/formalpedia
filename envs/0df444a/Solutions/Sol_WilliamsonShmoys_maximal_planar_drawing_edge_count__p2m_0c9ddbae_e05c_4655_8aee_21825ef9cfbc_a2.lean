-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_0c9ddbae_e05c_4655_8aee_21825ef9cfbc_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:07:15.556977+00:00
-- url     : https://prove2.me/submissions/f6e3f7a8-8060-4051-b335-5966c059c7c3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_1076f7d9_8cab_4c50_ba02_63cd640503d2_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ¬ ∃ N : SimpleGraph V,
      M.edgeSet ⊂ N.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn N) :
    3 * Fintype.card V = M.edgeSet.ncard + 6 := by
  obtain ⟨N, hsub, hNDraw, hNCount⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_1076f7d9_8cab_4c50_ba02_63cd640503d2_a1
      M hV hDraw
  have heq : M.edgeSet = N.edgeSet := Set.Subset.antisymm hsub (by
    intro e he
    by_contra hnot
    apply hMax
    refine ⟨N, ?_, hNDraw⟩
    change M.edgeSet ⊆ N.edgeSet ∧ ¬ N.edgeSet ⊆ M.edgeSet
    refine ⟨hsub, ?_⟩
    intro hNM
    exact hnot (hNM he))
  have hcard : M.edgeSet.ncard = N.edgeSet.ncard := congrArg Set.ncard heq
  omega