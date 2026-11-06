-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_maximal_planar_completion__p2m_9c07cfc8_fca3_44bb_9466_8248a8f68ed4_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T14:29:00.173954+00:00
-- url     : https://prove2.me/submissions/7f3592f8-f7ed-4374-9330-aaca0c21ae16

-- ID: 99f498ba-8796-40c9-a103-6d7b97940db4 | NAME: WilliamsonShmoys.exists_edge_maximal_planar_completion__p2m_9c07cfc8_fca3_44bb_9466_8248a8f68ed4_a1 | 未本地编译验证
import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option linter.unusedVariables false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M) : ∃ M' : SimpleGraph V, M ≤ M' ∧ WilliamsonShmoys.HasPlanarDrawingOn M' ∧ ∀ N : SimpleGraph V, M' ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M' := by
  classical
  let p : SimpleGraph V → Prop := fun K => M ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K
  have hpM : p M := ⟨le_rfl, hplanar⟩
  obtain ⟨M', hMM', hmax⟩ :=
    (Finite.exists_le_maximal (α := SimpleGraph V) (p := p) (a := M) hpM)
  rcases hmax with ⟨hpM', hmax'⟩
  refine ⟨M', hpM'.1, hpM'.2, ?_⟩
  intro N hM'N hN
  exact hmax' ⟨hpM'.1.trans hM'N, hN⟩ hM'N
