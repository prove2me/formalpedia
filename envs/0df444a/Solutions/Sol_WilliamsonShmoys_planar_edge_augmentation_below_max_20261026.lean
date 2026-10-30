-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_augmentation_below_max_20261026
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:45:06.157487+00:00
-- url     : https://prove2.me/submissions/2c7ca238-8318-4071-bed4-437c1d5a303f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_extension_exists_20261026
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_20261026

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hSmall : K.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ J : SimpleGraph V,
      K ≤ J ∧ J ≠ K ∧ WilliamsonShmoys.HasPlanarDrawingOn J := by
  obtain ⟨J, hKJ, hJ, hJmax⟩ :=
    WilliamsonShmoys.planar_extension_exists_20261026 K hK
  have hJcard :=
    WilliamsonShmoys.maximal_planar_edge_count_20261026 J hJ hV hJmax
  have hJK : J ≠ K := by
    intro hEq
    subst J
    omega
  exact ⟨J, hKJ, hJK, hJ⟩
