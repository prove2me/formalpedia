-- Prove2me | solution 1 for WilliamsonShmoys.exists_supergraph_maximal_edgeFinset_cardinality__p2m_2212fb5a_3b8b_4ff4_b66b_e1a858c8b349_a1
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-11T13:54:57.000071+00:00
-- url     : https://prove2.me/submissions/ef75628b-8817-47b8-9a4b-a87f18c51c22

import Mathlib

open SimpleGraph

set_option autoImplicit false

/-- Among all edge-supergraphs of `G` satisfying a downward-closed property, one has maximal
edge-set cardinality. -/
theorem solution {V : Type} [Fintype V] (P : SimpleGraph V → Prop)
    (hdown : ∀ {A B : SimpleGraph V}, A ≤ B → P B → P A)
    (G : SimpleGraph V) (hG : P G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ P H ∧
      ∃ (hHfin : Fintype H.edgeSet),
        ∀ K : SimpleGraph V, G ≤ K → P K → ∀ (hKfin : Fintype K.edgeSet),
          @Fintype.card K.edgeSet hKfin ≤ @Fintype.card H.edgeSet hHfin := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun K : SimpleGraph V => G ≤ K ∧ P K)
  have hS : S.Nonempty := ⟨G, by simp [S, hG]⟩
  obtain ⟨H, hHS, hmax⟩ :=
    Finset.exists_max_image S (fun K : SimpleGraph V => K.edgeSet.ncard) hS
  have hGH : G ≤ H := (Finset.mem_filter.mp hHS).2.1
  have hPH : P H := (Finset.mem_filter.mp hHS).2.2
  refine ⟨H, hGH, hPH, Fintype.ofFinite H.edgeSet, ?_⟩
  intro K hGK hPK hKfin
  have hKmem : K ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hGK, hPK⟩
  have hle : K.edgeSet.ncard ≤ H.edgeSet.ncard := hmax K hKmem
  rw [@Fintype.card_eq_nat_card _ hKfin, @Fintype.card_eq_nat_card _ (Fintype.ofFinite H.edgeSet),
    Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  exact hle
