-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_54bfa514_b5d2_470b_aa39_b977e5665440_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T14:59:20.411561+00:00
-- url     : https://prove2.me/submissions/432bfe87-60a0-4158-8095-4fc8b2203f54

-- ID: f0005e3e-fded-4b57-acf4-9bb9b5d27ef1 | NAME: WilliamsonShmoys.planar_drawing_maximal_extension__p2m_54bfa514_b5d2_470b_aa39_b977e5665440_a1 | 未本地编译验证
import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hPlanar : HasPlanarDrawingOn J) :
    ∃ N : SimpleGraph V,
      J ≤ N ∧
      HasPlanarDrawingOn N ∧
      (∀ M : SimpleGraph V, N ≤ M → HasPlanarDrawingOn M → M = N) := by
  classical
  let p : SimpleGraph V → Prop := fun H => J ≤ H ∧ HasPlanarDrawingOn H
  have hpJ : p J := ⟨le_rfl, hPlanar⟩
  obtain ⟨N, _hJN, hmax⟩ :=
    (Finite.exists_le_maximal (α := SimpleGraph V) (p := p) (a := J) hpJ)
  rcases hmax with ⟨hpN, hmax'⟩
  refine ⟨N, hpN.1, hpN.2, ?_⟩
  intro M hNM hM
  have hMN : M ≤ N := hmax' ⟨hpN.1.trans hNM, hM⟩ hNM
  exact le_antisymm hMN hNM
