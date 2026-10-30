-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_extension_exists__p2m_e74de359_8181_429e_92f3_9fe027354fb5_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:17:13.028532+00:00
-- url     : https://prove2.me/submissions/8b5779e6-035a-46f4-ae87-86aeea0cc1bf

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_exists_maximal_of_nonempty__p2m_7f3e1c59_fb8d_479f_ad2c_408c88d9882e_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : HasPlanarDrawingOn N) :
    exists K : SimpleGraph V, N ≤ K ∧ HasPlanarDrawingOn K ∧
      forall L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K := by
  let P : SimpleGraph V → Prop := fun G => N ≤ G ∧ HasPlanarDrawingOn G
  obtain ⟨K, hK, hmax⟩ :=
    WilliamsonShmoys.finite_exists_maximal_of_nonempty__p2m_7f3e1c59_fb8d_479f_ad2c_408c88d9882e_a1
      P ⟨N, le_rfl, hN⟩
  refine ⟨K, hK.1, hK.2, ?_⟩
  intro L hKL hL
  have hLK : L ≤ K := hmax L ⟨hK.1.trans hKL, hL⟩ hKL
  exact le_antisymm hLK hKL