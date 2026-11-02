-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count__p2m_63ad9a14_da0c_4363_acd0_29ef03d610e6_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:44:32.321202+00:00
-- url     : https://prove2.me/submissions/2bcd63bf-ae67-43dc-914e-4a9dfa1d03bb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_completion__p2m_d609182c_5b53_49cf_bf61_f0fd403543f8_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hn : 3 <= Fintype.card V)
    (hmax : ∀ N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N →
      M ≤ N →
      N = M) :
    M.edgeFinset.card = 3 * Fintype.card V - 6 := by
  classical
  obtain ⟨H, dH, hH, hsub, hcard⟩ :=
    WilliamsonShmoys.maximal_drawable_completion__p2m_d609182c_5b53_49cf_bf61_f0fd403543f8_a1
      M dM hM hn
  have heq : H = M := hmax H hH hsub
  subst H
  have hdec : dH = dM := Subsingleton.elim _ _
  rw [hdec] at hcard
  exact hcard