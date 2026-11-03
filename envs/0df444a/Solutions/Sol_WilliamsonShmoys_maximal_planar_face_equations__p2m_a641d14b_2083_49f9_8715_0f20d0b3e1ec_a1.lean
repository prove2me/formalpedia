-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_equations__p2m_a641d14b_2083_49f9_8715_0f20d0b3e1ec_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T13:08:26.532721+00:00
-- url     : https://prove2.me/submissions/6f97dc64-71aa-4638-a38e-62a8d0dcbf35

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_equation__p2m_addb50df_8cce_4ac7_84ef_2e1f35b931aa_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_triangular_incidence__p2m_addb50df_8cce_4ac7_84ef_2e1f35b931aa_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L → H ≤ L → L = H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     ∃ f : ℕ,
      Fintype.card V + f = H.edgeFinset.card + 2 ∧
        3 * f = 2 * H.edgeFinset.card) := by
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.maximal_planar_euler_equation__p2m_addb50df_8cce_4ac7_84ef_2e1f35b931aa_a1
      H hcard hdraw hmax
  refine ⟨f, hEuler, ?_⟩
  exact WilliamsonShmoys.maximal_planar_triangular_incidence__p2m_addb50df_8cce_4ac7_84ef_2e1f35b931aa_a1
    H hcard hdraw hmax f hEuler