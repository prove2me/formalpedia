-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_maximal__p2m_2f30e2d9_4845_4c04_a5c2_ea4608bfb1b9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:37:38.342127+00:00
-- url     : https://prove2.me/submissions/5f681a03-e7d8-4658-b0e2-ca2a5a3ccece

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_extension_maximal_by_measure__p2m_a06e74bc_2d14_4a85_b8d6_42f2136549b3_a1
import Theorems.Thm_edgeSet_ncard_strict_of_subset_ne__p2m_a06e74bc_2d14_4a85_b8d6_42f2136549b3_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ M : SimpleGraph V,
      Set.Subset G.edgeSet M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V,
        Set.Subset M.edgeSet N.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn N →
        N = M := by
  let R : SimpleGraph V → SimpleGraph V → Prop :=
    fun A B => Set.Subset A.edgeSet B.edgeSet
  let measure : SimpleGraph V → Nat := fun A => A.edgeSet.ncard
  have hstrict : ∀ A B : SimpleGraph V, R A B → A ≠ B → measure A < measure B := by
    intro A B hAB hne
    exact edgeSet_ncard_strict_of_subset_ne__p2m_a06e74bc_2d14_4a85_b8d6_42f2136549b3_a1 hAB hne
  obtain ⟨M, hGM, hM, hmax⟩ :=
    finite_extension_maximal_by_measure__p2m_a06e74bc_2d14_4a85_b8d6_42f2136549b3_a1
      R measure (fun H => WilliamsonShmoys.HasPlanarDrawingOn H)
      (fun A => Set.Subset.rfl) (by
        intro A B C hAB hBC
        exact Set.Subset.trans hAB hBC)
      hstrict G hG
  exact ⟨M, hGM, hM, fun N hMN hN => hmax N hMN hN⟩