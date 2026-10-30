-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_extension__p2m_6a3d0978_a2a8_418a_a56b_10e4c543dafd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:03:13.372821+00:00
-- url     : https://prove2.me/submissions/be4835da-f996-400d-a70b-f059377790e2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_nonempty_subset_has_maximal_element__p2m_7a02e70f_fc61_442e_a193_09698b981594_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (M : SimpleGraph V)
    (hM : P M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ P N ∧
      ∀ K : SimpleGraph V, N ≤ K → P K → K = N := by
  classical
  let s : SimpleGraph V → Prop := fun N => M ≤ N ∧ P N
  have hs : ∃ N, s N := ⟨M, le_rfl, hM⟩
  obtain ⟨N, hN, hmax⟩ :=
    WilliamsonShmoys.finite_nonempty_subset_has_maximal_element__p2m_7a02e70f_fc61_442e_a193_09698b981594_a1
      s hs
  refine ⟨N, hN.1, hN.2, ?_⟩
  intro K hNK hPK
  exact hmax K hNK ⟨le_trans hN.1 hNK, hPK⟩