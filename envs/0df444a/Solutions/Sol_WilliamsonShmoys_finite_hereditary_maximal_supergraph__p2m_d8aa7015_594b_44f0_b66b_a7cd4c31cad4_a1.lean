-- Prove2me | solution 1 for WilliamsonShmoys.finite_hereditary_maximal_supergraph__p2m_d8aa7015_594b_44f0_b66b_a7cd4c31cad4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T09:39:04.107818+00:00
-- url     : https://prove2.me/submissions/f294d330-6c9c-4fb7-9ad9-39d3d36c0fc5

import Mathlib

set_option autoImplicit false

theorem maxext {V : Type} [Fintype V] (R : SimpleGraph V → Prop) (M : SimpleGraph V)
    (hM : R M) :
    ∃ N : SimpleGraph V, Set.Subset M.edgeSet N.edgeSet ∧ R N ∧
      ∀ P : SimpleGraph V, Set.Subset N.edgeSet P.edgeSet → R P → P = N := by
  classical
  have hfin : Finite (SimpleGraph V) := inferInstance
  obtain ⟨N, hN, hmax⟩ := Set.Finite.exists_maximalFor (f := id) (s := {G : SimpleGraph V | M ≤ G ∧ R G})
    (Set.toFinite _) ⟨M, le_rfl, hM⟩
  refine ⟨N, SimpleGraph.edgeSet_mono hN.1, hN.2, fun P hP hRP => ?_⟩
  have hle : N ≤ P := by
    intro u v h
    have : s(u, v) ∈ P.edgeSet := hP (by simpa using h)
    simpa using this
  exact le_antisymm (hmax ⟨hN.1.trans hle, hRP⟩ hle) hle |>.symm.symm

theorem solution {V : Type} [Fintype V] [LinearOrder V] (R : SimpleGraph V → Prop) (hmono : ∀ {G H : SimpleGraph V}, Set.Subset G.edgeSet H.edgeSet → R H → R G) (N : SimpleGraph V) (hN : R N) : ∃ P : SimpleGraph V, Set.Subset N.edgeSet P.edgeSet ∧ R P ∧ ∀ Q : SimpleGraph V, Set.Subset P.edgeSet Q.edgeSet → R Q → Set.Subset Q.edgeSet P.edgeSet := by
  obtain ⟨P, h1, h2, h3⟩ := maxext R N hN
  refine ⟨P, h1, h2, fun Q hQ hRQ => ?_⟩
  exact le_of_eq (congrArg SimpleGraph.edgeSet (h3 Q hQ hRQ))
