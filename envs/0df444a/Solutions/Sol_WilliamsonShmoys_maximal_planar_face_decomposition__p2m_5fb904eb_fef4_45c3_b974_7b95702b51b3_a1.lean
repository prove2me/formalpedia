-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_decomposition__p2m_5fb904eb_fef4_45c3_b974_7b95702b51b3_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:00:52.46878+00:00
-- url     : https://prove2.me/submissions/eb01fb30-396f-437e-9423-ba77ae85be1e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_upper_bound__p2m_e194ab00_41b0_4b4f_af08_d9da373e3f16_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_e194ab00_41b0_4b4f_af08_d9da373e3f16_a1
import Theorems.Thm_WilliamsonShmoys_face_count_arithmetic__p2m_e194ab00_41b0_4b4f_af08_d9da373e3f16_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall H : SimpleGraph V, K <= H -> WilliamsonShmoys.HasPlanarDrawingOn H -> H <= K)
    (hV : 3 <= Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      3 * f = 2 * K.edgeSet.ncard := by
  have hupper := WilliamsonShmoys.maximal_planar_edge_upper_bound__p2m_e194ab00_41b0_4b4f_af08_d9da373e3f16_a1 K hK hV
  have hlower := WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_e194ab00_41b0_4b4f_af08_d9da373e3f16_a1 K hK hmax hV
  have hedge : 3 * Fintype.card V = K.edgeSet.ncard + 6 := by omega
  exact WilliamsonShmoys.face_count_arithmetic__p2m_e194ab00_41b0_4b4f_af08_d9da373e3f16_a1 (Fintype.card V) K.edgeSet.ncard hedge