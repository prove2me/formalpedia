-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_supergraph__p2m_6683070b_8f0f_4f85_989e_81cd2560323f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:58:28.070617+00:00
-- url     : https://prove2.me/submissions/80c42792-e66b-4e2b-9f19-0d24a55aa996

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Order.Preorder.Finite

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V,
        N.edgeSet ⊆ K.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        K.edgeSet ⊆ N.edgeSet := by
  classical
  let S : Set (SimpleGraph V) :=
    {N | M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N}
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := by
    refine ⟨M, ?_⟩
    change M ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M
    exact ⟨le_rfl, hM⟩
  obtain ⟨N, hNS, hNmax⟩ := hSfinite.exists_maximal hSnonempty
  refine ⟨N, SimpleGraph.edgeSet_mono hNS.1, hNS.2, ?_⟩
  intro K hNK hK
  have hNleK : N ≤ K := SimpleGraph.edgeSet_subset_edgeSet.mp hNK
  have hKS : K ∈ S := by
    change M ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K
    exact ⟨hNS.1.trans hNleK, hK⟩
  have hKleN : K ≤ N := hNmax hKS hNleK
  exact SimpleGraph.edgeSet_mono hKleN