-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_ef71f331_24e3_40c9_8157_32dae1795a54_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:07:19.892822+00:00
-- url     : https://prove2.me/submissions/4ae396b0-8b8c-4444-b4b0-3337b2406f4b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V),
        3 ≤ Fintype.card V →
        (∀ M : SimpleGraph V,
          L.edgeSet ⊆ M.edgeSet →
          HasPlanarDrawingOn M →
          M.edgeSet = L.edgeSet) →
        L.edgeSet.ncard = 3 * Fintype.card V - 6) := by
  intro h
  let L : SimpleGraph (Fin 5) := ⊤
  have hV : 3 ≤ Fintype.card (Fin 5) := by
    simp
  have hmaximal :
      ∀ M : SimpleGraph (Fin 5),
        L.edgeSet ⊆ M.edgeSet →
        HasPlanarDrawingOn M →
        M.edgeSet = L.edgeSet := by
    intro M hsub _
    apply Set.Subset.antisymm
    · simpa [L] using (SimpleGraph.edgeSet_subset_compl_diagSet (G := M))
    · exact hsub
  have hresult := h L hV hmaximal
  have hL : L = (⊤ : SimpleGraph (Fin 5)) := rfl
  have hcard : Fintype.card ((⊤ : SimpleGraph (Fin 5)).edgeSet) = 10 := by
    rw [SimpleGraph.card_edgeSet,
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
    norm_num [Nat.choose_two_right]
  have hcount : L.edgeSet.ncard = 10 := by
    rw [← Set.fintypeCard_eq_ncard]
    simpa [hL] using hcard
  rw [hcount] at hresult
  norm_num [Fintype.card_fin] at hresult
