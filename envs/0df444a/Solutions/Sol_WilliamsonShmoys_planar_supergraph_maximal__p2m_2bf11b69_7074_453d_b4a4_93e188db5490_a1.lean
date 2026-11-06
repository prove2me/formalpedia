-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_maximal__p2m_2bf11b69_7074_453d_b4a4_93e188db5490_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T14:32:58.084274+00:00
-- url     : https://prove2.me/submissions/211604fa-5ee8-4351-a1be-3fa27dc41ba0

-- ID: 10e5fa50-ae85-4d68-b666-509a03938328 | NAME: WilliamsonShmoys.planar_supergraph_maximal__p2m_2bf11b69_7074_453d_b4a4_93e188db5490_a1 | 未本地编译验证
import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hV : 3 <= Fintype.card V) : ∃ T : SimpleGraph V, HasPlanarDrawingOn T ∧ H ≤ T ∧ ∀ K : SimpleGraph V, HasPlanarDrawingOn K → T ≤ K → K ≤ T := by
  classical
  let p : SimpleGraph V → Prop := fun T => H ≤ T ∧ HasPlanarDrawingOn T
  have hpH0 : p H := ⟨le_rfl, hH⟩
  obtain ⟨T, _, hmax⟩ :=
    (Finite.exists_le_maximal (α := SimpleGraph V) (p := p) (a := H) hpH0)
  rcases hmax with ⟨hpT, hmax'⟩
  refine ⟨T, hpT.2, hpT.1, ?_⟩
  intro K hK hTK
  exact hmax' ⟨hpT.1.trans hTK, hK⟩ hTK
