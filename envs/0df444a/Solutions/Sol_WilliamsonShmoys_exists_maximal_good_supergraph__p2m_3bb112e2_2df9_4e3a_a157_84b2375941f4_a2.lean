-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_good_supergraph__p2m_3bb112e2_2df9_4e3a_a157_84b2375941f4_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:11:35.704949+00:00
-- url     : https://prove2.me/submissions/c6f87211-c173-4d33-b82c-725a788cf59d

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (P : SimpleGraph V) (Good : SimpleGraph V → Prop)
    (hP : Good P)
    (hsub : ∀ {G H : SimpleGraph V}, H ≤ G → Good G → Good H) :
    ∃ Q : SimpleGraph V, P ≤ Q ∧ Good Q ∧
      ∀ R : SimpleGraph V, Q ≤ R → Good R → R ≤ Q := by
  classical
  let p : SimpleGraph V → Prop := fun G => P ≤ G ∧ Good G
  have hp : ∃ G : SimpleGraph V, p G := ⟨P, le_rfl, hP⟩
  obtain ⟨Q, dQ, hQ⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists p).2 hp
  letI : DecidableRel Q.Adj := dQ
  refine ⟨Q, hQ.1.1, hQ.1.2, ?_⟩
  intro R hQR hR
  have hRprop : p R := ⟨hQ.1.1.trans hQR, hR⟩
  exact le_of_eq ((SimpleGraph.IsExtremal.le_iff_eq hQ hRprop).mp hQR).symm