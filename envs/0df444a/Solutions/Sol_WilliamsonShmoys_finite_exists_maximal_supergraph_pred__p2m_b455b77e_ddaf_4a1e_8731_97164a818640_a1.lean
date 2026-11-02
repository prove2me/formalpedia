-- Prove2me | solution 1 for WilliamsonShmoys.finite_exists_maximal_supergraph_pred__p2m_b455b77e_ddaf_4a1e_8731_97164a818640_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:19:21.930538+00:00
-- url     : https://prove2.me/submissions/0892e67c-1a10-4fa5-a55a-bc7cb577793a

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (P : SimpleGraph V) (D : SimpleGraph V → Prop)
    (hP : D P) :
    ∃ Q : SimpleGraph V,
      (∀ {u v : V}, P.Adj u v → Q.Adj u v) ∧
      D Q ∧
      (∀ R : SimpleGraph V,
        (∀ {u v : V}, Q.Adj u v → R.Adj u v) →
        D R →
        R = Q) := by
  classical
  let S : Set (SimpleGraph V) := {Q | P ≤ Q ∧ D Q}
  have hSfinite : S.Finite := Set.toFinite S
  have hSne : S.Nonempty := ⟨P, le_rfl, hP⟩
  obtain ⟨Q, hQmax⟩ := hSfinite.exists_maximal hSne
  rcases hQmax with ⟨hQmem, hmax⟩
  change P ≤ Q ∧ D Q at hQmem
  refine ⟨Q, ?_, hQmem.2, ?_⟩
  · intro u v huv
    exact (SimpleGraph.le_iff_adj.mp hQmem.1) u v huv
  · intro R hQR hR
    have hQRle : Q ≤ R :=
      SimpleGraph.le_iff_adj.mpr (by
        intro u v huv
        exact hQR huv)
    have hPRle : P ≤ R := hQmem.1.trans hQRle
    have hRmem : R ∈ S := ⟨hPRle, hR⟩
    have hRQ : R ≤ Q := hmax hRmem hQRle
    exact le_antisymm hRQ hQRle