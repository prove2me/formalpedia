-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_2c52a5e8_a177_4eaa_adc1_eeae3ac4d632_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:01:53.067819+00:00
-- url     : https://prove2.me/submissions/87ba69be-286e-4401-8a05-8bfef228b5b1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_completion__p2m_7eac73df_a948_4c33_96ae_30ffe17dadaf_a1
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall M' : SimpleGraph V, M <= M' ->
      WilliamsonShmoys.HasPlanarDrawingOn M' -> M' = M) :
    3 * Fintype.card V <= M.edgeSet.ncard + 6 := by
  obtain ⟨M', hle, hplanar', hcount⟩ :=
    WilliamsonShmoys.exists_planar_triangulation_completion__p2m_7eac73df_a948_4c33_96ae_30ffe17dadaf_a1
      M hplanar hcard
  have heq := hmax M' hle hplanar'
  subst M'
  omega