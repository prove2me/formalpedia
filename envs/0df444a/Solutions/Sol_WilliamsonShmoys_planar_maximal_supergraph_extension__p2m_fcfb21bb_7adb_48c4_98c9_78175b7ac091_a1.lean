-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_supergraph_extension__p2m_fcfb21bb_7adb_48c4_98c9_78175b7ac091_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:45:33.584473+00:00
-- url     : https://prove2.me/submissions/5485c073-d3f0-489d-8c16-401697113627

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_exists_maximal_hereditary_supergraph__p2m_4af6ea92_4c22_435e_a0b4_a6c72b25ac6d_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 <= Fintype.card V) :
    Exists fun N : SimpleGraph V =>
      (forall {u v : V}, M.Adj u v -> N.Adj u v) /\
      WilliamsonShmoys.HasPlanarDrawingOn N /\
      (forall P : SimpleGraph V,
        (forall {u v : V}, N.Adj u v -> P.Adj u v) ->
        WilliamsonShmoys.HasPlanarDrawingOn P -> P = N) := by
  have hhered :
      forall {G H : SimpleGraph V},
        (forall {u v : V}, H.Adj u v -> G.Adj u v) ->
        WilliamsonShmoys.HasPlanarDrawingOn G ->
        WilliamsonShmoys.HasPlanarDrawingOn H := by
    intro G H hsub hG
    rcases hG with ⟨p, arc, hinj, hedge, hcross⟩
    refine ⟨p, arc, hinj, ?_, ?_⟩
    · intro u v huv hadj
      exact hedge u v huv (hsub hadj)
    · intro u v x y huv hxy hadj₁ hadj₂ hne t ht s hs hEq
      exact hcross u v x y huv hxy (hsub hadj₁) (hsub hadj₂) hne t ht s hs hEq
  obtain ⟨N, hMN, hN, hmax⟩ :=
    exists_maximal_hereditary_supergraph__p2m_4af6ea92_4c22_435e_a0b4_a6c72b25ac6d_a1
      WilliamsonShmoys.HasPlanarDrawingOn hhered M hM
  exact ⟨N, hMN, hN, fun P hNP hP => hmax P hNP hP⟩