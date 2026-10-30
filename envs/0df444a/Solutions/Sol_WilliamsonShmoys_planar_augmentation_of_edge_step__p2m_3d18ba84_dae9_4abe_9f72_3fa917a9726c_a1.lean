-- Prove2me | solution 1 for WilliamsonShmoys.planar_augmentation_of_edge_step__p2m_3d18ba84_dae9_4abe_9f72_3fa917a9726c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:19:14.595997+00:00
-- url     : https://prove2.me/submissions/6fe5eb9b-70cd-4b93-82cd-ff7680b83d8a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (hV : 3 <= Fintype.card V)
    (step : ∀ (G : SimpleGraph V), HasPlanarDrawingOn G → ¬ G.Connected →
      ∃ K : SimpleGraph V,
        G ≤ K ∧ HasPlanarDrawingOn K ∧ G.edgeSet.ncard < K.edgeSet.ncard)
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H.edgeSet.ncard <= K.edgeSet.ncard ∧
      HasPlanarDrawingOn K ∧ K.Connected := by
  classical
  let M : Nat := Nat.card (Sym2 V)
  have edge_bound (G : SimpleGraph V) : G.edgeSet.ncard ≤ M := by
    simpa [M] using Set.ncard_le_card G.edgeSet
  have aux : ∀ m : Nat, ∀ G : SimpleGraph V,
      HasPlanarDrawingOn G → M - G.edgeSet.ncard = m →
      ∃ K : SimpleGraph V,
        G.edgeSet.ncard ≤ K.edgeSet.ncard ∧
        HasPlanarDrawingOn K ∧ K.Connected := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro G hG hmeasure
        by_cases hconn : G.Connected
        · exact ⟨G, le_rfl, hG, hconn⟩
        · obtain ⟨K, hGK, hK, hlt⟩ := step G hG hconn
          have hle : G.edgeSet.ncard ≤ K.edgeSet.ncard := le_of_lt hlt
          have hboundK : K.edgeSet.ncard ≤ M := edge_bound K
          have hmeasureK : M - K.edgeSet.ncard < m := by
            rw [← hmeasure]
            omega
          obtain ⟨L, hKL, hL, hLconn⟩ := ih (M - K.edgeSet.ncard) hmeasureK K hK rfl
          exact ⟨L, le_trans hle hKL, hL, hLconn⟩
  exact aux (M - H.edgeSet.ncard) H hH rfl