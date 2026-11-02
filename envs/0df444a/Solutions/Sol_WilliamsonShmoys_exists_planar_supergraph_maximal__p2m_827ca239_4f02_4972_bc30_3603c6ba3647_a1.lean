-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_supergraph_maximal__p2m_827ca239_4f02_4972_bc30_3603c6ba3647_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:24:25.377201+00:00
-- url     : https://prove2.me/submissions/add06527-d471-45ec-a46c-bc545f18684e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) [DecidableRel L.Adj]
    (P : SimpleGraph V → Prop) (hL : P L) :
    ∃ H : SimpleGraph V, ∃ (dH : DecidableRel H.Adj),
      (letI : DecidableRel H.Adj := dH; L.edgeFinset ⊆ H.edgeFinset ∧ P H ∧
        (∀ K : SimpleGraph V, (∀ u v, H.Adj u v → K.Adj u v) → P K →
          ∀ u v, K.Adj u v → H.Adj u v)) := by
  classical
  let S : Set (SimpleGraph V) := {G | L ≤ G ∧ P G}
  have hS : S.Nonempty := ⟨L, le_rfl, hL⟩
  have hfinite : ((fun G : SimpleGraph V => G.edgeFinset.card) '' S).Finite := by
    apply (Set.finite_Icc 0 ((Fintype.card V).choose 2)).subset
    rintro n ⟨G, hG, rfl⟩
    exact ⟨Nat.zero_le _, SimpleGraph.card_edgeFinset_le_card_choose_two⟩
  obtain ⟨H, hH, hmax⟩ :=
    Set.Finite.exists_maximalFor' (f := fun G : SimpleGraph V => G.edgeFinset.card)
      (s := S) hfinite hS
  refine ⟨H, inferInstance, ?_⟩
  refine ⟨SimpleGraph.edgeFinset_subset_edgeFinset.mpr hH.1, hH.2, ?_⟩
  intro K hHK hPK u v huv
  have hHK' : H ≤ K := hHK
  have hK : K ∈ S := ⟨hH.1.trans hHK', hPK⟩
  have hKH : K ≤ H := by
    by_contra hn
    have hlt : H < K := lt_iff_le_not_ge.mpr ⟨hHK', hn⟩
    have hcard : H.edgeFinset.card < K.edgeFinset.card :=
      Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
    have hle : K.edgeFinset.card ≤ H.edgeFinset.card :=
      hmax hK (Nat.le_of_lt hcard)
    exact (Nat.not_le_of_gt hcard hle)
  exact hKH huv
