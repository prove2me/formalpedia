-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_count_identities__p2m_24cd5df2_f06e_484a_a9e0_671b5163ec2a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:49:51.745143+00:00
-- url     : https://prove2.me/submissions/7d4593b9-ddea-47d3-a8c7-7f590898f294

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_2c52a5e8_a177_4eaa_adc1_eeae3ac4d632_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_2c52a5e8_a177_4eaa_adc1_eeae3ac4d632_a2

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall M' : SimpleGraph V, M <= M' ->
      WilliamsonShmoys.HasPlanarDrawingOn M' -> M' = M) :
    ∃ f : ℕ, 2 * M.edgeSet.ncard = 3 * f ∧
      Fintype.card V + f = M.edgeSet.ncard + 2 := by
  have hupper := WilliamsonShmoys.planar_edge_upper_bound__p2m_2c52a5e8_a177_4eaa_adc1_eeae3ac4d632_a2
    M hplanar hcard
  have hlower := WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_2c52a5e8_a177_4eaa_adc1_eeae3ac4d632_a2
    M hplanar hcard hmax
  have hedge : M.edgeSet.ncard + 6 = 3 * Fintype.card V := by omega
  refine ⟨2 * Fintype.card V - 4, ?_⟩
  constructor <;> omega