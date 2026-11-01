-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_supergraph_of_downward_property__p2m_b2333537_9e91_4fe0_a355_0d6ef469faac_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:06:33.76376+00:00
-- url     : https://prove2.me/submissions/100b3e77-07bf-40c7-8aab-9b2745c3aff3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (K : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hK : P K)
    (hdown : ∀ {G H : SimpleGraph V},
      (∀ u v, G.Adj u v → H.Adj u v) → P H → P G) :
    ∃ M : SimpleGraph V,
      (∀ u v, K.Adj u v → M.Adj u v) ∧
      P M ∧
      (∀ N : SimpleGraph V,
        (∀ u v, M.Adj u v → N.Adj u v) →
        P N →
        (∀ u v, N.Adj u v → M.Adj u v)) := by
  classical
  let S : Set (SimpleGraph V) := {G | K ≤ G ∧ P G}
  have hS : S.Nonempty := ⟨K, le_rfl, hK⟩
  obtain ⟨M, hMmem, hMmax⟩ := S.toFinite.exists_maximal hS
  rcases hMmem with ⟨hKM, hPM⟩
  refine ⟨M, ?_, hPM, ?_⟩
  · intro u v huv
    exact hKM huv
  · intro N hMN hPN
    have hKN : K ≤ N := le_trans hKM hMN
    have hNmem : N ∈ S := ⟨hKN, hPN⟩
    have hNM : N ≤ M := hMmax hNmem hMN
    intro u v huv
    exact hNM huv