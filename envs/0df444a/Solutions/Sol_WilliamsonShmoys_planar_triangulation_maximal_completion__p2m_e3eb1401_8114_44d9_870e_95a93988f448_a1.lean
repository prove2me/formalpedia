-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_maximal_completion__p2m_e3eb1401_8114_44d9_870e_95a93988f448_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:58:42.297318+00:00
-- url     : https://prove2.me/submissions/de487e37-f222-4a45-b798-cb048477246c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    ∃ L : SimpleGraph V,
      HasPlanarDrawingOn L ∧
      (∀ u v, G.Adj u v → L.Adj u v) ∧
      (∀ M : SimpleGraph V, HasPlanarDrawingOn M →
        (∀ u v, L.Adj u v → M.Adj u v) →
        ∀ u v, M.Adj u v → L.Adj u v) := by
  classical
  let S : Set (SimpleGraph V) :=
    {M | HasPlanarDrawingOn M ∧ ∀ u v, G.Adj u v → M.Adj u v}
  have hS : S.Nonempty := by
    refine ⟨G, hG, ?_⟩
    intro u v huv
    exact huv
  obtain ⟨L, hL, hmax⟩ := (Set.toFinite S).exists_maximal hS
  refine ⟨L, hL.1, hL.2, ?_⟩
  intro M hM hLM u v hMuv
  have hLM' : L ≤ M := hLM
  have hMcandidate : M ∈ S := by
    refine ⟨hM, ?_⟩
    intro a b hab
    exact hLM' (hL.2 a b hab)
  have hML : M ≤ L := hmax hMcandidate hLM'
  exact hML hMuv