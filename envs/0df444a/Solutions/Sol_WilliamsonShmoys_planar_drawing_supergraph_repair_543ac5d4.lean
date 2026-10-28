-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_supergraph_repair_543ac5d4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T05:41:38.66849+00:00
-- url     : https://prove2.me/submissions/41d031ad-3560-4d03-ac8c-a540d74086d4

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_bounded_nat_predicate_has_maximum
import Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_le_card_sym2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hS : WilliamsonShmoys.HasPlanarDrawingOn S) :
    ∃ T : SimpleGraph V,
      S ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧
        ∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U →
          U.edgeSet.ncard ≤ T.edgeSet.ncard := by
  classical
  let P : Nat → Prop := fun n =>
    ∃ T : SimpleGraph V, S ≤ T ∧
      WilliamsonShmoys.HasPlanarDrawingOn T ∧ T.edgeSet.ncard = n
  have hp : ∃ n, P n := by
    exact ⟨S.edgeSet.ncard, S, le_rfl, hS, rfl⟩
  have hb : ∀ n, P n → n ≤ Fintype.card (Sym2 V) := by
    intro n hn
    rcases hn with ⟨T, hST, hT, hcount⟩
    rw [← hcount]
    exact WilliamsonShmoys.edgeSet_ncard_le_card_sym2 T
  obtain ⟨m, hm, hmax⟩ :=
    WilliamsonShmoys.bounded_nat_predicate_has_maximum P hp
      (Fintype.card (Sym2 V)) hb
  rcases hm with ⟨T, hST, hT, hcount⟩
  refine ⟨T, hST, hT, ?_⟩
  intro U hTU hU
  have hle : U.edgeSet.ncard ≤ m :=
    hmax U.edgeSet.ncard ⟨U, le_trans hST hTU, hU, rfl⟩
  simpa [hcount] using hle