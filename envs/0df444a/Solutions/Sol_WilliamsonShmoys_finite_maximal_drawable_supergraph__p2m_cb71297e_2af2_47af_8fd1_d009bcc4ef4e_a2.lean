-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_drawable_supergraph__p2m_cb71297e_2af2_47af_8fd1_d009bcc4ef4e_a2
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T14:58:15.0368+00:00
-- url     : https://prove2.me/submissions/f673f461-127e-4652-a2f1-eae85f15a1b9

-- ID: 5c5ff357-b4a7-43ef-ab24-576229740c5b | NAME: WilliamsonShmoys.finite_maximal_drawable_supergraph__p2m_cb71297e_2af2_47af_8fd1_d009bcc4ef4e_a2 | 未本地编译验证
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ HasPlanarDrawingOn H ∧
      K.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      ∀ J : SimpleGraph V, H ≤ J → HasPlanarDrawingOn J → J ≤ H := by
  classical
  let p : SimpleGraph V → Prop := fun H => K ≤ H ∧ HasPlanarDrawingOn H
  have hpK : p K := ⟨le_rfl, hK⟩
  obtain ⟨H, _hKH, hmax⟩ :=
    (Finite.exists_le_maximal (α := SimpleGraph V) (p := p) (a := K) hpK)
  rcases hmax with ⟨hpH, hmax'⟩
  have hsub : K.edgeSet ⊆ H.edgeSet :=
    SimpleGraph.edgeSet_subset_edgeSet.mpr hpH.1
  have hfin : H.edgeSet.Finite := Set.toFinite _
  refine ⟨H, hpH.1, hpH.2, Set.ncard_le_ncard hsub hfin, ?_⟩
  intro J hHJ hJ
  exact hmax' ⟨hpH.1.trans hHJ, hJ⟩ hHJ
