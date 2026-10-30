-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_supergraph_of_downward_closed_property__p2m_1df87970_57df_486f_9fe9_1f5bd1c60a90_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:34:24.852168+00:00
-- url     : https://prove2.me/submissions/2a7b3ec5-dbdc-4ee7-8037-972c524a50d8

import Mathlib

theorem solution
    {V : Type} [Fintype V]
    (H : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hP : P H)
    (hdown : ∀ {G K : SimpleGraph V}, G ≤ K → P K → P G) :
    ∃ J : SimpleGraph V,
      H ≤ J ∧ P J ∧
      ∀ K : SimpleGraph V, J ≤ K → P K → K = J := by
  classical
  obtain ⟨J, hHJ, hmax⟩ := Finite.exists_le_maximal (p := P) hP
  refine ⟨J, hHJ, hmax.1, ?_⟩
  intro K hJK hPK
  exact (hmax.eq_of_le hPK hJK).symm