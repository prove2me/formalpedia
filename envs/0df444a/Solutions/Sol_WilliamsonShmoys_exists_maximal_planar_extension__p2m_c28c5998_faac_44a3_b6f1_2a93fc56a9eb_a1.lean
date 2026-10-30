-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_extension__p2m_c28c5998_faac_44a3_b6f1_2a93fc56a9eb_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:10:42.924998+00:00
-- url     : https://prove2.me/submissions/68ca595c-4a63-41f3-a31c-2f9a1ae7fa9e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_finite_extension__p2m_8cd16ded_735f_4df7_8b84_93c58f4228da_a1
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hH : HasPlanarDrawingOn H) :
    ∃ J : SimpleGraph V, H ≤ J ∧ HasPlanarDrawingOn J ∧
      ∀ K : SimpleGraph V, J ≤ K → HasPlanarDrawingOn K → K = J := by
  obtain ⟨J, hHJ, hJ, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_finite_extension__p2m_8cd16ded_735f_4df7_8b84_93c58f4228da_a1
      H HasPlanarDrawingOn hH
  exact ⟨J, hHJ, hJ, fun K hJK hK => hmax K hJK hK⟩