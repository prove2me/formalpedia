-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_maximal__p2m_43831d01_c2a2_47cc_baf7_12299ab7bdf8_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T17:29:56.706078+00:00
-- url     : https://prove2.me/submissions/3b7dda97-fe1f-44a4-83f8-e642e32cccc6

-- ID: 3647f07c-750e-4c3e-8be8-ca29b1e4d823 | NAME: WilliamsonShmoys.planar_supergraph_maximal__p2m_43831d01_c2a2_47cc_baf7_12299ab7bdf8_a1 | 未本地编译验证
import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) (hV : 3 <= Fintype.card V) : ∃ H : SimpleGraph V, K <= H ∧ HasPlanarDrawingOn H ∧ (∀ J : SimpleGraph V, H <= J → HasPlanarDrawingOn J → J <= H) := by
  classical
  let p : SimpleGraph V → Prop := fun H => K ≤ H ∧ HasPlanarDrawingOn H
  have hpK : p K := ⟨le_rfl, hK⟩
  obtain ⟨H, _hKH, hmax⟩ :=
    (Finite.exists_le_maximal (α := SimpleGraph V) (p := p) (a := K) hpK)
  rcases hmax with ⟨hpH, hmax'⟩
  refine ⟨H, hpH.1, hpH.2, ?_⟩
  intro J hHJ hJ
  exact hmax' ⟨hpH.1.trans hHJ, hJ⟩ hHJ
