-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_augmentation_maximal_extension__p2m_a95b2e09_031c_4e18_b347_423c7cdf2425_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T20:25:11.111668+00:00
-- url     : https://prove2.me/submissions/a5fc5fbd-0f15-423e-965c-551ab9b7f9ee

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option linter.unusedVariables false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hconn : H.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ J : SimpleGraph V, H ≤ J ∧ J.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn J ∧
      ∀ K : SimpleGraph V, J ≤ K →
        WilliamsonShmoys.HasPlanarDrawingOn K → K = J := by
  classical
  let p : SimpleGraph V → Prop :=
    fun J => H ≤ J ∧ WilliamsonShmoys.HasPlanarDrawingOn J
  have hpH : p H := ⟨le_rfl, hdraw⟩
  obtain ⟨J, _hHJ, hmax⟩ :=
    (Finite.exists_le_maximal (α := SimpleGraph V) (p := p) (a := H) hpH)
  rcases hmax with ⟨hpJ, hmax'⟩
  refine ⟨J, hpJ.1, SimpleGraph.Connected.mono hpJ.1 hconn, hpJ.2, ?_⟩
  intro K hJK hK
  have hKJ : K ≤ J := hmax' ⟨hpJ.1.trans hJK, hK⟩ hJK
  exact le_antisymm hKJ hJK
