-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_certificate__p2m_2b02d0f4_e4a5_4246_8c79_3e972b456778_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:18:05.172068+00:00
-- url     : https://prove2.me/submissions/2d55bda4-6b30-4691-8cd5-493ed7494f92
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_be551f10_f0c9_4808_ad70_62595a008c11_a2
import Theorems.Thm_WilliamsonShmoys_planar_face_arithmetic__p2m_be551f10_f0c9_4808_ad70_62595a008c11_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ P : SimpleGraph V, N ≤ P → WilliamsonShmoys.HasPlanarDrawingOn P → P = N) :
    letI : DecidableRel N.Adj := Classical.decRel N.Adj
    ∃ (F : Type) (_ : Fintype F) (length : F → ℕ),
      (∑ f : F, (length f : ℤ) = 2 * (N.edgeFinset.card : ℤ)) ∧
      ((Fintype.card V : ℤ) - (N.edgeFinset.card : ℤ) + (Fintype.card F : ℤ) = 2) ∧
      (∀ f : F, length f = 3) ∧
      ((∑ f : F, (length f : ℤ)) = 3 * (Fintype.card F : ℤ)) := by
  classical
  have hedge := WilliamsonShmoys.maximal_planar_edge_count__p2m_be551f10_f0c9_4808_ad70_62595a008c11_a2
    N hN hcard hmax
  exact WilliamsonShmoys.planar_face_arithmetic__p2m_be551f10_f0c9_4808_ad70_62595a008c11_a2
    (Fintype.card V) N.edgeFinset.card hcard hedge