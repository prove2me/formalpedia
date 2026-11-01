-- Prove2me | solution 1 for WilliamsonShmoys.strict_edgeSet_ncard_of_strict_extension__p2m_f914dab2_91be_415e_a370_d761f8bbdaba_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:59:35.450356+00:00
-- url     : https://prove2.me/submissions/49c4c921-a07e-476c-8f05-26c7739d3bb0

import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H K : SimpleGraph V)
    (hHK : H ≤ K)
    (hKH : ¬ (K ≤ H)) :
    H.edgeSet.ncard < K.edgeSet.ncard := by
  have hlt : H < K := by
    constructor
    · exact hHK
    · exact hKH
  exact Set.ncard_lt_ncard (SimpleGraph.edgeSet_ssubset_edgeSet.mpr hlt)