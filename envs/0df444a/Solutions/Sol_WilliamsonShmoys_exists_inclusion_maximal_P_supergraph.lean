-- Prove2me | solution 1 for WilliamsonShmoys.exists_inclusion_maximal_P_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T13:30:30.707273+00:00
-- url     : https://prove2.me/submissions/70ae4666-20e6-4eb6-9c39-484893da3b0f

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Set.Card

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V) (P : SimpleGraph V → Prop)
    (hP : P W) :
    ∃ H : SimpleGraph V,
      W ≤ H ∧ P H ∧ ∀ K : SimpleGraph V, W ≤ K → H ≤ K → P K → K = H := by
  classical
  let admissible : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun G => W ≤ G ∧ P G)
  have hW : W ∈ admissible := by
    simp [admissible, hP]
  obtain ⟨H, hH, hmax⟩ :=
    Finset.exists_max_image admissible
      (fun G : SimpleGraph V => G.edgeFinset.card) ⟨W, hW⟩
  refine ⟨H, ?_, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hH).2.1
  · exact (Finset.mem_filter.mp hH).2.2
  · intro K hWK hHK hPK
    have hK : K ∈ admissible := by
      simp [admissible, hWK, hPK]
    by_contra hne
    have hHKne : H ≠ K := fun h => hne h.symm
    have hlt : H < K := lt_of_le_of_ne hHK hHKne
    have hcard : H.edgeFinset.card < K.edgeFinset.card :=
      Finset.card_lt_card
        (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
    exact (Nat.not_lt_of_ge (hmax K hK)) hcard