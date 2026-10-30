-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_22eb0949_0e91_449a_8343_64436b0a0efb_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:06:08.316997+00:00
-- url     : https://prove2.me/submissions/c3d9f806-af75-4722-a47d-aeda815effa5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_drawable_supergraphs__p2m_34323cd1_374d_4357_8256_7d86cba1e73f_a1
import Theorems.Thm_exists_maximal_of_finite_set__p2m_34323cd1_374d_4357_8256_7d86cba1e73f_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ T : SimpleGraph V, L ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧
      ∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T := by
  classical
  let S : Set (SimpleGraph V) :=
    {T | L ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T}
  have hS : S.Finite := by
    exact WilliamsonShmoys.finite_drawable_supergraphs__p2m_34323cd1_374d_4357_8256_7d86cba1e73f_a1 L
  have hSne : S.Nonempty := ⟨L, le_rfl, hL⟩
  obtain ⟨T, hTS, hTmax⟩ :=
    exists_maximal_of_finite_set__p2m_34323cd1_374d_4357_8256_7d86cba1e73f_a1
      S hS hSne
  refine ⟨T, hTS.1, hTS.2, ?_⟩
  intro U hTU hU
  have hUS : U ∈ S := ⟨le_trans hTS.1 hTU, hU⟩
  exact hTmax U hUS hTU