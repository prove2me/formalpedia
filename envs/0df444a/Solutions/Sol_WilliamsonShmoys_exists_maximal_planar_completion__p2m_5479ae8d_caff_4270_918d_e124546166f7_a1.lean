-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_completion__p2m_5479ae8d_caff_4270_918d_e124546166f7_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T22:51:32.243315+00:00
-- url     : https://prove2.me/submissions/dc4562bc-3848-4364-bebc-dc23633eb367

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Order.Preorder.Finite

set_option autoImplicit false

open SimpleGraph

lemma planarDrawingOn_mono_aux
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V}
    (hGH : G ≤ H)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by
  rcases hH with ⟨p, arc, hp, hedge, hcross⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hadj
    exact hedge u v huv (hGH hadj)
  · intro u v x y huv hxy hadj₁ hadj₂ hne t ht s hs hts
    exact hcross u v x y huv hxy (hGH hadj₁) (hGH hadj₂) hne t ht s hs hts

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ N : SimpleGraph V,
      L ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ M : SimpleGraph V, N ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ N := by
  classical
  let P : Set (SimpleGraph V) :=
    {M | L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M}
  have hfinite : P.Finite := Set.toFinite P
  obtain ⟨N, hN, hmax⟩ := hfinite.exists_maximal ⟨L, le_rfl, hL⟩
  refine ⟨N, hN.1, hN.2, ?_⟩
  intro M hNM hM
  have hMP : M ∈ P := ⟨hN.1.trans hNM, hM⟩
  exact hmax hMP hNM