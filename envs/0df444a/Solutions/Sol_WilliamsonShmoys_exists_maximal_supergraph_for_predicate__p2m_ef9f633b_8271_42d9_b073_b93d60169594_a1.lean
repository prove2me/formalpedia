-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_supergraph_for_predicate__p2m_ef9f633b_8271_42d9_b073_b93d60169594_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T20:47:07.85301+00:00
-- url     : https://prove2.me/submissions/d6640e3d-2c8c-4db9-9f28-3ae8666bc367

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : P H) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      H.edgeFinset ⊆ K.edgeFinset ∧
      P K ∧
      ∀ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
        K.edgeFinset ⊆ L.edgeFinset → P L →
          L.edgeFinset = K.edgeFinset := by
  classical
  letI : DecidableRel H.Adj := dH
  let encode : SimpleGraph V → (V → V → Bool) :=
    fun G x y => decide (G.Adj x y)
  have hencode : Function.Injective encode := by
    intro G G' h
    ext x y
    have hxy := congrFun (congrFun h x) y
    by_cases hG : G.Adj x y <;> by_cases hG' : G'.Adj x y <;>
      simp [encode, hG, hG'] at hxy ⊢
  letI : Finite (SimpleGraph V) := Finite.of_injective encode hencode
  letI : Fintype (SimpleGraph V) := Fintype.ofFinite (SimpleGraph V)
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => H.edgeFinset ⊆ G.edgeFinset ∧ P G
  have hHmem : H ∈ S := by
    simp [S, hH]
  obtain ⟨K, hKmem, hKmax⟩ :=
    Finset.exists_max_image S (fun G => G.edgeFinset.card) ⟨H, hHmem⟩
  have hKS : H.edgeFinset ⊆ K.edgeFinset ∧ P K :=
    (Finset.mem_filter.mp hKmem).2
  refine ⟨K, inferInstance, hKS.1, hKS.2, ?_⟩
  intro L dL hKL hPL
  letI : DecidableRel L.Adj := Classical.decRel _
  have hKL' : K.edgeFinset ⊆ L.edgeFinset := by
    simpa using hKL
  have hHL : H.edgeFinset ⊆ L.edgeFinset := hKS.1.trans hKL'
  have hLmem : L ∈ S :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hHL, hPL⟩
  have hcard : L.edgeFinset.card ≤ K.edgeFinset.card := hKmax L hLmem
  by_contra hneq
  have hs : K.edgeFinset ⊂ L.edgeFinset :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hKL', by intro heq; apply hneq; simpa using heq.symm⟩
  have hlt := Finset.card_lt_card hs
  omega
