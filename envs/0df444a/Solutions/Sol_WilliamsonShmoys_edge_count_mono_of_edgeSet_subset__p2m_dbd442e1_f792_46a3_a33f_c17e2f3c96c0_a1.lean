-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_mono_of_edgeSet_subset__p2m_dbd442e1_f792_46a3_a33f_c17e2f3c96c0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:22:29.974398+00:00
-- url     : https://prove2.me/submissions/616c7936-c0c8-4ba2-b560-3fb1c8e1f6ea

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (H K : SimpleGraph V)
    (hsub : H.edgeSet ⊆ K.edgeSet) :
    H.edgeSet.ncard ≤ K.edgeSet.ncard := by
  classical
  have hK : K.edgeSet.Finite :=
    (Set.finite_univ : (Set.univ : Set (Sym2 V)).Finite).subset
      (Set.subset_univ _)
  exact Set.ncard_le_ncard hsub hK