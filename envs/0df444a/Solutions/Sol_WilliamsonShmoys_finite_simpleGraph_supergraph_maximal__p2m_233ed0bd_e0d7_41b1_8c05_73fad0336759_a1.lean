-- Prove2me | solution 1 for WilliamsonShmoys.finite_simpleGraph_supergraph_maximal__p2m_233ed0bd_e0d7_41b1_8c05_73fad0336759_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:31:35.612928+00:00
-- url     : https://prove2.me/submissions/b5bded8f-bc89-4c34-884a-8608237f7846

import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_maximal_extension_of_finite_preorder__p2m_7fc18aad_d07a_49bb_b01c_abff1eddf2b3_a2

set_option autoImplicit false

open SimpleGraph

theorem solution
    {V : Type} [Fintype V]
    (H : SimpleGraph V) (P : SimpleGraph V → Prop) (hH : P H) :
    ∃ J : SimpleGraph V,
      And (P J)
        (And (H ≤ J)
          (∀ K : SimpleGraph V,
            P K → J ≤ K → K ≤ J)) := by
  classical
  exact WilliamsonShmoys.exists_maximal_extension_of_finite_preorder__p2m_7fc18aad_d07a_49bb_b01c_abff1eddf2b3_a2
    H P hH