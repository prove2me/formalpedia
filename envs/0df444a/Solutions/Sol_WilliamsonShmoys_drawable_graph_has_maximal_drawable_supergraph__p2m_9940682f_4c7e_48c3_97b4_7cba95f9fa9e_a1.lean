-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_has_maximal_drawable_supergraph__p2m_9940682f_4c7e_48c3_97b4_7cba95f9fa9e_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T14:58:47.178364+00:00
-- url     : https://prove2.me/submissions/ce93dba3-1048-42b8-92bd-b6491e8669e1

-- ID: ae4c30e4-5c41-43ac-8ef4-2c08b5f2ff70 | NAME: WilliamsonShmoys.drawable_graph_has_maximal_drawable_supergraph__p2m_9940682f_4c7e_48c3_97b4_7cba95f9fa9e_a1 | 未本地编译验证
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K) :
    ∃ (L : SimpleGraph V) (hLdec : DecidableRel L.Adj),
      K ≤ L ∧ HasPlanarDrawingOn L ∧
      (∀ M : SimpleGraph V, L < M → ¬ HasPlanarDrawingOn M) := by
  classical
  let p : SimpleGraph V → Prop := fun G => K ≤ G ∧ HasPlanarDrawingOn G
  have hpK : p K := ⟨le_rfl, hK⟩
  obtain ⟨L, _hKL, hmax⟩ :=
    (Finite.exists_le_maximal (α := SimpleGraph V) (p := p) (a := K) hpK)
  rcases hmax with ⟨hpL, hmax'⟩
  refine ⟨L, Classical.decRel L.Adj, hpL.1, hpL.2, ?_⟩
  intro M hLM hM
  have hML : M ≤ L := hmax' ⟨hpL.1.trans (le_of_lt hLM), hM⟩ (le_of_lt hLM)
  exact (not_le_of_gt hLM) hML
