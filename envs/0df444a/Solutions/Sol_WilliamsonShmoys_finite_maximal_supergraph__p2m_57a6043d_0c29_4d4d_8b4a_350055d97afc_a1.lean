-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_supergraph__p2m_57a6043d_0c29_4d4d_8b4a_350055d97afc_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:43:52.70671+00:00
-- url     : https://prove2.me/submissions/a0b788e8-635e-4c9b-884a-392d47f16a10

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (P : SimpleGraph V → Prop) (hK : P K) :
    ∃ H : SimpleGraph V, ∃ dH : DecidableRel H.Adj,
      K ≤ H ∧ P H ∧ Nat.le K.edgeFinset.card H.edgeFinset.card ∧
        ∀ J : SimpleGraph V, K ≤ J → P J → H ≤ J → J = H := by
  classical
  letI : DecidableRel K.Adj := dK
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => K ≤ G ∧ P G
  have hSne : S.Nonempty := by
    refine ⟨K, ?_⟩
    simp [S, hK]
  obtain ⟨H, hHS, hHmax⟩ :=
    Finset.exists_max_image S (fun G => G.edgeFinset.card) hSne
  have hHprops : K ≤ H ∧ P H := by
    have hmem := Finset.mem_filter.mp hHS
    exact hmem.2
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  refine ⟨H, Classical.decRel H.Adj, hHprops.1, hHprops.2, ?_, ?_⟩
  · have hKsub : K.edgeFinset ⊆ H.edgeFinset := by
      exact SimpleGraph.edgeFinset_mono hHprops.1
    exact Finset.card_le_card hKsub
  · intro J hKJ hPJ hHJ
    letI : DecidableRel J.Adj := Classical.decRel J.Adj
    have hJmem : J ∈ S := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ J, ⟨hKJ, hPJ⟩⟩
    have hcard : J.edgeFinset.card ≤ H.edgeFinset.card := hHmax J hJmem
    have hsub : H.edgeFinset ⊆ J.edgeFinset :=
      SimpleGraph.edgeFinset_mono hHJ
    have hedges : H.edgeFinset = J.edgeFinset :=
      Finset.eq_of_subset_of_card_le hsub hcard
    have hedgeSet : H.edgeSet = J.edgeSet := by
      have h := congrArg (fun E : Finset (Sym2 V) => (E : Set (Sym2 V))) hedges
      simpa only [SimpleGraph.coe_edgeFinset] using h
    exact SimpleGraph.edgeSet_inj.mp hedgeSet.symm