-- Prove2me | solution 1 for WilliamsonShmoys_finite_maximal_planar_supergraph__p2m_6c35d7b0_b5ac_47cb_81ba_67341f778754_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T15:00:26.451926+00:00
-- url     : https://prove2.me/submissions/2668b559-598a-4566-98f1-9f35b6939380

-- ID: 475324d9-e323-4e9d-912b-397241bc4fc3 | NAME: WilliamsonShmoys_finite_maximal_planar_supergraph__p2m_6c35d7b0_b5ac_47cb_81ba_67341f778754_a1 | 未本地编译验证
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V,
      G.edgeSet ⊆ K.edgeSet ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        K.edgeSet ⊆ L.edgeSet → HasPlanarDrawingOn L →
        ¬ K.edgeSet ⊂ L.edgeSet := by
  classical
  let p : SimpleGraph V → Prop := fun H => G ≤ H ∧ HasPlanarDrawingOn H
  have hpG : p G := ⟨le_rfl, hG⟩
  obtain ⟨K, _hGK, hmax⟩ :=
    (Finite.exists_le_maximal (α := SimpleGraph V) (p := p) (a := G) hpG)
  rcases hmax with ⟨hpK, hmax'⟩
  refine ⟨K, SimpleGraph.edgeSet_subset_edgeSet.mpr hpK.1, hpK.2, ?_⟩
  intro L hKL hL hss
  have hKLe : K ≤ L := SimpleGraph.edgeSet_subset_edgeSet.mp hKL
  have hLK : L ≤ K := hmax' ⟨hpK.1.trans hKLe, hL⟩ hKLe
  exact hss.2 (SimpleGraph.edgeSet_subset_edgeSet.mpr hLK)
